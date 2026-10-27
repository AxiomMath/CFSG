module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveTransv

public section

open Subgroup CFSG.Open

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G]

@[expose] def conjAutNorm (W : Subgroup G) : normalizer (W : Set G) →* MulAut W where
  toFun n :=
    { toFun := fun v => ⟨n * v * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 v).mp v.2⟩
      invFun := fun v => ⟨(n : G)⁻¹ * v * n, by
        have := (mem_normalizer_iff.mp (inv_mem n.2) v).mp v.2
        rwa [inv_inv] at this⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun v w => Subtype.ext (by simp only [coe_mul]; group) }
  map_one' := MulEquiv.ext fun v => Subtype.ext (by simp)
  map_mul' n m := MulEquiv.ext fun v => Subtype.ext (by simp [mul_assoc])

theorem conjAutNorm_apply (W : Subgroup G) (n : normalizer (W : Set G)) (v : W) :
    ((conjAutNorm W n v : W) : G) = n * v * (n : G)⁻¹ := rfl

theorem conj_eq_inv_of_fpf [Finite G] {F : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ normalizer (F : Set G)) (hfix : ∀ f ∈ F, t * f * t⁻¹ = f → f = 1) :
    ∀ f ∈ F, t * f * t⁻¹ = f⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcm : ∀ x ∈ F, t * x * t⁻¹ ∈ F := fun x hx => (mem_normalizer_iff.mp htN x).mp hx
  let φ : F → F := fun x => ⟨(x : G)⁻¹ * (t * x * t⁻¹), F.mul_mem (F.inv_mem x.2) (hcm x x.2)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : (x : G)⁻¹ * (t * x * t⁻¹) = (y : G)⁻¹ * (t * y * t⁻¹) := congrArg Subtype.val hxy
    have h2 : t * ((y : G) * (x : G)⁻¹) * t⁻¹ = (y : G) * (x : G)⁻¹ := by
      calc t * ((y : G) * (x : G)⁻¹) * t⁻¹ = (y : G) * ((y : G)⁻¹ * (t * y * t⁻¹)) *
          (t * x * t⁻¹)⁻¹ := by group
        _ = (y : G) * ((x : G)⁻¹ * (t * x * t⁻¹)) * (t * x * t⁻¹)⁻¹ := by rw [h1]
        _ = (y : G) * (x : G)⁻¹ := by group
    have h3 := hfix _ (F.mul_mem y.2 (F.inv_mem x.2)) h2
    apply Subtype.ext
    calc (x : G) = ((y : G) * (x : G)⁻¹)⁻¹ * y := by group
      _ = y := by rw [h3, inv_one, one_mul]
  have hφs : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ
  intro f hf
  obtain ⟨x, hx⟩ := hφs ⟨f, hf⟩
  have hxf : (x : G)⁻¹ * (t * x * t⁻¹) = f := congrArg Subtype.val hx
  rw [← hxf, hti]
  calc t * ((x : G)⁻¹ * (t * x * t)) * t = t * (x : G)⁻¹ * t * x * (t * t) := by group
    _ = t * (x : G)⁻¹ * t * x := by rw [ht, mul_one]
    _ = ((x : G)⁻¹ * (t * x * t))⁻¹ := by
        rw [show ((x : G)⁻¹ * (t * x * t))⁻¹ = t⁻¹ * (x : G)⁻¹ * t⁻¹ * x by group, hti]

theorem smul_eq_of_pow_eq_one {K α : Type*} [Group K] [Finite K] [MulAction K α] {f : K}
    {p k : ℕ} (hp : p.Prime) (hf : f ^ p ^ k = 1) {S : Set α} (hSfin : S.Finite)
    (hS : S.ncard < p) (hSf : ∀ a ∈ S, f • a ∈ S) {a : α} (ha : a ∈ S) : f • a = a := by
  have hpow : ∀ n : ℕ, f ^ n • a ∈ S := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]; exact ha
    | succ n ih => rw [pow_succ', mul_smul]; exact hSf _ ih
  have horb : MulAction.orbit (zpowers f) a ⊆ S := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    exact hpow n
  have hidx := MulAction.index_stabilizer (zpowers f) a
  have hdvd : (MulAction.stabilizer (zpowers f) a).index ∣ p ^ k := by
    refine (Subgroup.index_dvd_card _).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hf
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hle : (MulAction.stabilizer (zpowers f) a).index < p := by
    rw [hidx]
    exact lt_of_le_of_lt (Set.ncard_le_ncard horb hSfin) hS
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hle
    have : p ≤ p ^ j := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.mpr hj0)
    omega
  rw [hj0, pow_zero, Subgroup.index_eq_one] at hj
  have hfs : (⟨f, mem_zpowers f⟩ : zpowers f) ∈ MulAction.stabilizer (zpowers f) a := by
    rw [hj]; exact mem_top _
  exact hfs

theorem false_of_transitive_odd [Finite G] {W V₀ Y B : Subgroup G} (hWe : IsElemAbelian 2 W)
    (hW16 : Nat.card W = 16) (hV₀W : V₀ ≤ W) (hV₀4 : Nat.card V₀ = 4)
    (hYN : Y ≤ normalizer (W : Set G)) (hY2 : ∀ n ∈ Y, IsPGroup 2 (zpowers n) → n ∈ W)
    (htrans : ∀ a ∈ W, ∀ b ∈ W, a ≠ 1 → b ≠ 1 → ∃ n ∈ Y, n * a * n⁻¹ = b)
    (hBN : B ≤ normalizer (W : Set G)) (hBY : ∀ r ∈ B, ∀ n ∈ Y, r * n * r⁻¹ ∈ Y)
    (hB4 : Nat.card B = 4) (hB2 : ∀ r ∈ B, r * r = 1)
    (hfix : ∀ r ∈ B, r ≠ 1 → ∀ v ∈ W, r * v * r⁻¹ = v → v ∈ V₀)
    (hcomm : ∀ r ∈ B, ∀ v ∈ W, v⁻¹ * (r * v * r⁻¹) ∈ V₀)
    (hBV₀ : ∀ r ∈ B, ∀ v ∈ V₀, r * v * r⁻¹ = v) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set ρ := conjAutNorm W with hρ
  set H : Subgroup (MulAut W) := (Y.subgroupOf (normalizer (W : Set G))).map ρ with hHdef
  have hρW : ∀ n : normalizer (W : Set G), (n : G) ∈ W → ρ n = 1 := by
    intro n hn
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [hρ, conjAutNorm_apply, MulAut.one_apply]
    have := congrArg Subtype.val (hWe.1.is_comm.comm ⟨n, hn⟩ ⟨v, v.2⟩)
    simp only [coe_mul] at this
    rw [this]
    group
  have hHodd : ¬ 2 ∣ Nat.card H := by
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨n, hnY, hnx⟩ := mem_map.mp x.2
    have hnY' : (n : G) ∈ Y := mem_subgroupOf.mp hnY
    have hx' : orderOf (ρ n) = 2 := by rw [hnx, Subgroup.orderOf_coe, hx]
    have hx2 : ρ n * ρ n = 1 := by rw [← sq, ← hx', pow_orderOf_eq_one]
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    have hn2 : (n : G) ^ b ∈ W := by
      refine hY2 _ (pow_mem hnY' b) ?_
      have hpow : ((n : G) ^ b) ^ 2 ^ a = 1 := by
        rw [← pow_mul, mul_comm, ← hab, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have h1 : ρ (n ^ b) = 1 := hρW _ (by rw [Subgroup.coe_pow]; exact hn2)
    obtain ⟨c, rfl⟩ := hb
    have h3 : ρ n ^ (2 * c + 1) = ρ n := by
      rw [pow_succ, pow_mul, sq, hx2, one_pow, one_mul]
    rw [map_pow, h3] at h1
    have : orderOf (ρ n) = 1 := by rw [h1, orderOf_one]
    omega
  have hW2 : ∀ v ∈ W, v * v = 1 := fun v hv => by rw [← sq]; exact hWe.2 v hv
  have hV₀2 : ∀ v ∈ V₀, v * v = 1 := fun v hv => hW2 v (hV₀W hv)
  obtain ⟨w₀, hw₀, hw₀1, -⟩ := exists_ne_one_ne hV₀4 hV₀2 (one_mem V₀)
  have hH5 : 5 ∣ Nat.card H := by
    have horb : MulAction.orbit H (⟨w₀, hV₀W hw₀⟩ : W) = {v : W | v ≠ 1} := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩ hx1
        apply hw₀1
        have : (x : MulAut W) (⟨w₀, hV₀W hw₀⟩ : W) = (x : MulAut W) 1 := by
          rw [map_one]; exact hx1
        exact congrArg Subtype.val ((x : MulAut W).injective this)
      · intro hv
        have hv1 : (v : G) ≠ 1 := fun he => hv (Subtype.ext he)
        obtain ⟨n, hnY, hn⟩ := htrans w₀ (hV₀W hw₀) v v.2 hw₀1 hv1
        refine ⟨⟨ρ ⟨n, hYN hnY⟩, ⟨⟨n, hYN hnY⟩, mem_subgroupOf.mpr hnY, rfl⟩⟩, ?_⟩
        exact Subtype.ext hn
    have hidx := MulAction.index_stabilizer H (⟨w₀, hV₀W hw₀⟩ : W)
    rw [horb, show {v : W | v ≠ 1} = ({1}ᶜ : Set W) from rfl, Set.ncard_compl,
      Set.ncard_singleton, hW16] at hidx
    have h15 : (MulAction.stabilizer H (⟨w₀, hV₀W hw₀⟩ : W)).index ∣ Nat.card H :=
      Subgroup.index_dvd_card _
    rw [hidx] at h15
    exact (show (5 : ℕ) ∣ 16 - 1 by norm_num).trans h15
  have hBH : ∀ r (hr : r ∈ B), ∀ x ∈ H, ρ ⟨r, hBN hr⟩ * x * (ρ ⟨r, hBN hr⟩)⁻¹ ∈ H := by
    rintro r hr _ ⟨n, hnY, rfl⟩
    refine ⟨⟨r, hBN hr⟩ * n * ⟨r, hBN hr⟩⁻¹, mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul,
      map_inv]⟩
    exact hBY r hr n (mem_subgroupOf.mp hnY)
  set Bb : Subgroup (MulAut W) := (B.subgroupOf (normalizer (W : Set G))).map ρ with hBbdef
  have hBbN : Bb ≤ normalizer (H : Set (MulAut W)) := by
    rintro _ ⟨⟨r, hrN⟩, hrB, rfl⟩
    have hrB' : r ∈ B := mem_subgroupOf.mp hrB
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hBH r hrB' x, fun hx => ?_⟩
    have := hBH r⁻¹ (inv_mem hrB') _ hx
    have e : (ρ ⟨r⁻¹, hBN (inv_mem hrB')⟩) = (ρ ⟨r, hrN⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rwa [e, inv_inv, show (ρ ⟨r, hrN⟩)⁻¹ * (ρ ⟨r, hrN⟩ * x * (ρ ⟨r, hrN⟩)⁻¹) * ρ ⟨r, hrN⟩ = x by
      group] at this
  have hBb2 : IsPGroup 2 Bb := by
    refine IsPGroup.map (IsPGroup.of_card (n := 2) ?_) ρ
    rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv, hB4]
    rfl
  let _ : MulDistribMulAction Bb H :=
    MulDistribMulAction.compHom H ((conjAutNorm H).comp (inclusion hBbN))
  have : Fact (IsPGroup 2 Bb) := ⟨hBb2⟩
  obtain ⟨F, hFinv⟩ := CFSG.exists_invariant_sylow (G := H) (A := Bb) (p := 2) (q := 5)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hHodd)
  set F' : Subgroup (MulAut W) := (F : Subgroup H).map H.subtype with hF'def
  have hF'H : F' ≤ H := map_subtype_le _
  have hF'N : ∀ r (hr : r ∈ B), ρ ⟨r, hBN hr⟩ ∈ normalizer (F' : Set (MulAut W)) := by
    intro r hr
    have hb : ρ ⟨r, hBN hr⟩ ∈ Bb := ⟨⟨r, hBN hr⟩, mem_subgroupOf.mpr hr, rfl⟩
    have key : ∀ x ∈ F', ρ ⟨r, hBN hr⟩ * x * (ρ ⟨r, hBN hr⟩)⁻¹ ∈ F' := by
      rintro _ ⟨x, hxF, rfl⟩
      have h1 := (hFinv.invariant ⟨_, hb⟩ x).mp hxF
      exact ⟨_, h1, rfl⟩
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key x, fun hx => ?_⟩
    obtain ⟨y, hyF, hyx⟩ := hx
    have hxH : x ∈ H := by
      have h1 := hBH r⁻¹ (inv_mem hr) _ (hF'H ⟨y, hyF, hyx⟩)
      have e : (ρ ⟨r⁻¹, hBN (inv_mem hr)⟩) = (ρ ⟨r, hBN hr⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rwa [e, inv_inv, show (ρ ⟨r, hBN hr⟩)⁻¹ * (ρ ⟨r, hBN hr⟩ * x * (ρ ⟨r, hBN hr⟩)⁻¹) *
        ρ ⟨r, hBN hr⟩ = x by group] at h1
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    have e : (⟨_, hb⟩ : Bb) • (⟨x, hxH⟩ : H) = y := Subtype.ext (by
      change ρ ⟨r, hBN hr⟩ * x * (ρ ⟨r, hBN hr⟩)⁻¹ = (y : MulAut W)
      exact hyx.symm)
    exact (hFinv.invariant ⟨_, hb⟩ ⟨x, hxH⟩).mpr (by rw [e]; exact hyF)
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f ∈ F', f ≠ 1 := by
    have hcard : 5 ≤ Nat.card (F : Subgroup H) := by
      rw [Sylow.card_eq_multiplicity]
      have hpos : 0 < (Nat.card H).factorization 5 :=
        (Nat.Prime.factorization_pos_of_dvd (by norm_num) Nat.card_pos.ne' hH5)
      calc 5 = 5 ^ 1 := (pow_one 5).symm
        _ ≤ 5 ^ (Nat.card H).factorization 5 := Nat.pow_le_pow_right (by norm_num) hpos
    by_contra hcon
    push Not at hcon
    have hbot : (F : Subgroup H) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have := hcon _ ⟨x, hx, rfl⟩
      exact mem_bot.mpr (Subtype.ext this)
    rw [hbot, card_bot] at hcard
    omega
  obtain ⟨r₁, hr₁, hr₁1, -⟩ := exists_ne_one_ne hB4 hB2 (one_mem B)
  obtain ⟨r₂, hr₂, hr₂1, hr₂r₁⟩ := exists_ne_one_ne hB4 hB2 hr₁
  have hr₁₂ : r₁ * r₂ ≠ 1 := fun he => hr₂r₁ (by
    calc r₂ = r₁⁻¹ * (r₁ * r₂) := by group
      _ = r₁ := by rw [he, mul_one]; exact inv_eq_of_mul_eq_one_right (hB2 r₁ hr₁))
  have hρ2 : ∀ r (hr : r ∈ B), ρ ⟨r, hBN hr⟩ * ρ ⟨r, hBN hr⟩ = 1 := by
    intro r hr
    rw [← map_mul, show (⟨r, hBN hr⟩ * ⟨r, hBN hr⟩ : normalizer (W : Set G)) = 1 from
      Subtype.ext (hB2 r hr), map_one]
  obtain ⟨r, hr, hr1, f, hfF, hf1, hrf⟩ : ∃ r, ∃ hr : r ∈ B, r ≠ 1 ∧ ∃ f ∈ F', f ≠ 1 ∧
      ρ ⟨r, hBN hr⟩ * f * (ρ ⟨r, hBN hr⟩)⁻¹ = f := by
    by_cases h1 : ∃ f ∈ F', f ≠ 1 ∧ ρ ⟨r₁, hBN hr₁⟩ * f * (ρ ⟨r₁, hBN hr₁⟩)⁻¹ = f
    · exact ⟨r₁, hr₁, hr₁1, h1⟩
    by_cases h2 : ∃ f ∈ F', f ≠ 1 ∧ ρ ⟨r₂, hBN hr₂⟩ * f * (ρ ⟨r₂, hBN hr₂⟩)⁻¹ = f
    · exact ⟨r₂, hr₂, hr₂1, h2⟩
    push Not at h1 h2
    have hi₁ := conj_eq_inv_of_fpf (hρ2 r₁ hr₁) (hF'N r₁ hr₁)
      (fun f hf hff => by_contra fun hne => h1 f hf hne hff)
    have hi₂ := conj_eq_inv_of_fpf (hρ2 r₂ hr₂) (hF'N r₂ hr₂)
      (fun f hf hff => by_contra fun hne => h2 f hf hne hff)
    refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, hr₁₂, f₀, hf₀F, hf₀1, ?_⟩
    have e : ρ ⟨r₁ * r₂, hBN (mul_mem hr₁ hr₂)⟩ = ρ ⟨r₁, hBN hr₁⟩ * ρ ⟨r₂, hBN hr₂⟩ := by
      rw [← map_mul]
      rfl
    rw [e, show ρ ⟨r₁, hBN hr₁⟩ * ρ ⟨r₂, hBN hr₂⟩ * f₀ * (ρ ⟨r₁, hBN hr₁⟩ * ρ ⟨r₂, hBN hr₂⟩)⁻¹ =
      (ρ ⟨r₁, hBN hr₁⟩ * (ρ ⟨r₂, hBN hr₂⟩ * f₀ * (ρ ⟨r₂, hBN hr₂⟩)⁻¹)⁻¹ *
        (ρ ⟨r₁, hBN hr₁⟩)⁻¹)⁻¹ by group, hi₂ f₀ hf₀F, inv_inv, hi₁ f₀ hf₀F, inv_inv]
  set t := ρ ⟨r, hBN hr⟩ with htdef
  have htf : t * f = f * t := by
    calc t * f = t * f * t⁻¹ * t := by group
      _ = f * t := by rw [hrf]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, f ^ 5 ^ k = 1 := by
    obtain ⟨y, hyF, rfl⟩ := hfF
    obtain ⟨k, hk⟩ := F.isPGroup' ⟨y, hyF⟩
    refine ⟨k, ?_⟩
    have h1 : y ^ 5 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [← map_pow, h1, map_one]
  have ht_apply : ∀ u : W, ((t u : W) : G) = r * u * r⁻¹ := fun u => rfl
  have htV₀ : ∀ u : W, (u : G) ∈ V₀ → t u = u := fun u hu =>
    Subtype.ext (by rw [ht_apply]; exact hBV₀ r hr u hu)
  have htf_apply : ∀ u : W, t (f u) = f (t u) := fun u => by
    rw [← MulAut.mul_apply, htf, MulAut.mul_apply]
  have hfV₀ : ∀ u : W, (u : G) ∈ V₀ → ((f u : W) : G) ∈ V₀ := by
    intro u hu
    refine hfix r hr hr1 _ (f u).2 ?_
    rw [← ht_apply, htf_apply, htV₀ u hu]
  have hfix₀ : ∀ u : W, (u : G) ∈ V₀ → f u = u := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
    set S : Set W := {v : W | (v : G) ∈ V₀ ∧ v ≠ 1} with hSdef
    have hS4 : S.ncard < 5 := by
      have hle : S ⊆ (V₀.subgroupOf W : Set W) := fun v hv => hv.1
      have h1 := Set.ncard_le_ncard hle
      have h2 : (V₀.subgroupOf W : Set W).ncard = 4 := by
        rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
          Nat.card_congr (subgroupOfEquivOfLe hV₀W).toEquiv, hV₀4]
      omega
    have hSf : ∀ v ∈ S, f • v ∈ S := by
      rintro v ⟨hv, hv1⟩
      refine ⟨hfV₀ v hv, fun he => hv1 ?_⟩
      have : f v = f 1 := by rw [map_one]; exact he
      exact f.injective this
    exact smul_eq_of_pow_eq_one (Nat.prime_five) hk (Set.toFinite S) hS4 hSf ⟨hu, hu1⟩
  have hφ : ∀ u : W, ((u⁻¹ * t u : W) : G) ∈ V₀ := fun u => by
    rw [coe_mul, coe_inv, ht_apply]
    exact hcomm r hr u u.2
  have hcomW : ∀ a b : W, a * b = b * a := fun a b => hWe.1.is_comm.comm a b
  have hcoset : ∀ v : W, ((v⁻¹ * f v : W) : G) ∈ V₀ := by
    intro v
    set u := v⁻¹ * f v with hudef
    have hfv : f v = v * u := by rw [hudef]; group
    have h1 : f (v⁻¹ * t v) = v⁻¹ * t v := hfix₀ _ (hφ v)
    rw [map_mul, map_inv, ← htf_apply, hfv, map_mul] at h1
    have h2 : u⁻¹ * t u = 1 := by
      have h3 : (v * u)⁻¹ * (t v * t u) = (v⁻¹ * t v) * (u⁻¹ * t u) := by
        calc (v * u)⁻¹ * (t v * t u) = u⁻¹ * (v⁻¹ * t v) * t u := by group
          _ = (v⁻¹ * t v) * u⁻¹ * t u := by rw [hcomW u⁻¹ (v⁻¹ * t v)]
          _ = (v⁻¹ * t v) * (u⁻¹ * t u) := by group
      rw [h3] at h1
      exact mul_left_cancel (h1.trans (mul_one _).symm)
    have h4 : t u = u := by
      calc t u = u * (u⁻¹ * t u) := by group
        _ = u := by rw [h2, mul_one]
    refine hfix r hr hr1 _ u.2 ?_
    rw [← ht_apply, h4]
  have hff : f * f = 1 := by
    refine MulEquiv.ext fun v => ?_
    rw [MulAut.mul_apply, MulAut.one_apply]
    have hu := hcoset v
    obtain ⟨u, hudef⟩ : ∃ u : W, u = v⁻¹ * f v := ⟨_, rfl⟩
    rw [← hudef] at hu
    have hfv : f v = v * u := by rw [hudef]; group
    have hfu : f u = u := hfix₀ u hu
    have hu2 : u * u = 1 := Subtype.ext (by rw [coe_mul, coe_one]; exact hV₀2 _ hu)
    rw [hfv, map_mul, hfv, hfu, mul_assoc, hu2, mul_one]
  apply hf1
  have h2 : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hff)
  have h5 : orderOf f ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime 2 (5 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf f = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h5
  exact orderOf_eq_one_iff.mp h1

end CFSG.ComponentClassification.RankTwoAltFive
