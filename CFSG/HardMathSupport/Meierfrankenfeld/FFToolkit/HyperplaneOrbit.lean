module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Hyperplanes
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

section Norm

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

noncomputable local instance : Fintype (MulAut W) := Fintype.ofFinite _

theorem range_normHom (hW : ∀ w : W, w * w = 1) {U : Subgroup (MulAut W)}
    (hodd : Odd (Nat.card U)) : (normHom U).range = fixV U := by
  ext v
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    exact normHom_mem_fixV U w
  · intro hv
    exact ⟨v, normHom_of_mem_fixV hW hodd hv⟩

theorem card_ker_normHom_mul (hW : ∀ w : W, w * w = 1) {U : Subgroup (MulAut W)}
    (hodd : Odd (Nat.card U)) :
    Nat.card (fixV U) * Nat.card (normHom U).ker = Nat.card W := by
  rw [← range_normHom hW hodd, mul_comm]
  exact Subgroup.card_ker_mul_card_range (normHom U)

theorem fixV_inf_ker_normHom (hW : ∀ w : W, w * w = 1) {U : Subgroup (MulAut W)}
    (hodd : Odd (Nat.card U)) : fixV U ⊓ (normHom U).ker = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hv
  have := normHom_of_mem_fixV hW hodd h1
  rw [MonoidHom.mem_ker.1 h2] at this
  exact Subgroup.mem_bot.2 this.symm

open scoped Classical in
theorem map_ker_normHom {U : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (U : Set (MulAut W))) {w : W} (hw : w ∈ (normHom U).ker) :
    g w ∈ (normHom U).ker := by
  rw [MonoidHom.mem_ker] at hw ⊢
  have hconj : ∀ d : U, g⁻¹ * (d : MulAut W) * g ∈ U := by
    intro d
    have := Subgroup.mem_set_normalizer_iff.1 hg (g⁻¹ * (d : MulAut W) * g)
    have e : g * (g⁻¹ * (d : MulAut W) * g) * g⁻¹ = d := by group
    rw [e] at this
    exact this.2 d.2
  have hconj' : ∀ d : U, g * (d : MulAut W) * g⁻¹ ∈ U := fun d =>
    (Subgroup.mem_set_normalizer_iff.1 hg d).1 d.2
  let e : U ≃ U :=
    { toFun := fun d => ⟨g⁻¹ * (d : MulAut W) * g, hconj d⟩
      invFun := fun d => ⟨g * (d : MulAut W) * g⁻¹, hconj' d⟩
      left_inv := fun d => Subtype.ext (by simp [mul_assoc])
      right_inv := fun d => Subtype.ext (by simp [mul_assoc]) }
  rw [normHom_apply]
  have h1 : ∀ d : U, (d : MulAut W) (g w) = g (((e d : U) : MulAut W) w) := by
    intro d
    show (d : MulAut W) (g w) = g ((g⁻¹ * (d : MulAut W) * g) w)
    simp [MulAut.mul_apply]
  simp only [h1]
  rw [← map_prod]
  have h2 : ∏ d : U, ((e d : U) : MulAut W) w = ∏ d : U, (d : MulAut W) w :=
    Fintype.prod_equiv e _ _ (fun _ => rfl)
  rw [h2, ← normHom_apply, hw, map_one]

end Norm

section Hyperplane

variable {W : Type} [CommGroup W]

@[expose] noncomputable def actOnSub {A : Subgroup (MulAut W)} {K : Subgroup W}
    (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K) : ↥A →* MulAut ↥K :=
  (CFSG.Quasithin.resHom K).comp (A.subtype.codRestrict (stabSub K) (fun a => by
    intro u
    refine ⟨fun h => ?_, fun h => hKA a a.2 u h⟩
    have := hKA a⁻¹ (A.inv_mem a.2) _ h
    simpa using this))

theorem actOnSub_apply {A : Subgroup (MulAut W)} {K : Subgroup W}
    (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K) (a : A) (k : K) :
    ((actOnSub hKA a k : K) : W) = (a : MulAut W) k := rfl

@[expose] noncomputable def hyperplaneHom (𝒟 : Finset (Subgroup (MulAut W))) (K : Subgroup W) :
    (∀ D : 𝒟, ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) →* W :=
  ∏ D : 𝒟, (fixV (D : Subgroup (MulAut W)) ⊓ K).subtype.comp
    (Pi.evalMonoidHom (fun D : 𝒟 => ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) D)

theorem hyperplaneHom_apply (𝒟 : Finset (Subgroup (MulAut W))) (K : Subgroup W)
    (x : ∀ D : 𝒟, ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) :
    hyperplaneHom 𝒟 K x = ∏ D : 𝒟, ((x D : ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) : W) := by
  simp [hyperplaneHom, MonoidHom.finsetProd_apply]

theorem hyperplaneHom_mem (𝒟 : Finset (Subgroup (MulAut W))) (K : Subgroup W)
    (x : ∀ D : 𝒟, ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) : hyperplaneHom 𝒟 K x ∈ K := by
  rw [hyperplaneHom_apply]
  exact Subgroup.prod_mem _ fun D _ => (Subgroup.mem_inf.1 (x D).2).2

open scoped Classical in
theorem normHom_eq_one_of_sup_of_mem [Finite W] {A D D' : Subgroup (MulAut W)} {K : Subgroup W}
    (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K) (hfix : fixV A ⊓ K = ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hDA : D ≤ A) (hD'A : D' ≤ A) (hsup : D ⊔ D' = A)
    {v : W} (hv : v ∈ fixV D) (hvK : v ∈ K) : normHom D' v = 1 := by
  have hu' : normHom D' v ∈ fixV D' := normHom_mem_fixV D' v
  have hu : normHom D' v ∈ fixV D := by
    rw [mem_fixV]
    intro g hg
    rw [normHom_apply, map_prod]
    refine Finset.prod_congr rfl fun d _ => ?_
    have hcomm : g * (d : MulAut W) = (d : MulAut W) * g := hAc g (hDA hg) d (hD'A d.2)
    have := congrArg (fun m : MulAut W => m v) hcomm
    simp only [MulAut.mul_apply] at this
    rw [this, mem_fixV.1 hv g hg]
  have hK : normHom D' v ∈ K := by
    rw [normHom_apply]
    exact Subgroup.prod_mem _ fun d _ => hKA d (hD'A d.2) v hvK
  have : normHom D' v ∈ fixV (D ⊔ D') := by rw [fixV_sup]; exact ⟨hu, hu'⟩
  rw [hsup] at this
  have h2 : normHom D' v ∈ fixV A ⊓ K := Subgroup.mem_inf.2 ⟨this, hK⟩
  rw [hfix, Subgroup.mem_bot] at h2
  exact h2

theorem hyperplaneHom_injective [Finite W] (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A : Subgroup (MulAut W)} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAp : ∀ a ∈ A, a ^ p = 1) {K : Subgroup W} (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K)
    (hfix : fixV A ⊓ K = ⊥) (𝒟 : Finset (Subgroup (MulAut W)))
    (h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p) :
    Function.Injective (hyperplaneHom 𝒟 K) := by
  classical
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hDodd : ∀ D : 𝒟, Odd (Nat.card (D : Subgroup (MulAut W))) := fun D =>
    odd_card_of_pow_eq_one hodd fun d hd => hAp d (((h𝒟 D).1 D.2).1 hd)
  rw [injective_iff_map_eq_one]
  intro x hx
  funext D₀
  have key := congrArg (normHom (D₀ : Subgroup (MulAut W))) hx
  rw [hyperplaneHom_apply, map_one, map_prod] at key
  rw [Finset.prod_eq_single D₀] at key
  · rw [normHom_of_mem_fixV hW (hDodd D₀) (Subgroup.mem_inf.1 (x D₀).2).1] at key
    exact Subtype.ext key
  · intro D _ hD
    have hDm := (h𝒟 D).1 D.2
    have hD₀m := (h𝒟 D₀).1 D₀.2
    exact normHom_eq_one_of_sup_of_mem hKA hfix hAc hDm.1 hD₀m.1
      (sup_eq_of_relIndex_eq_prime hDm.1 hD₀m.1 hDm.2 hD₀m.2 fun h => hD (Subtype.ext h))
      (Subgroup.mem_inf.1 (x D).2).1 (Subgroup.mem_inf.1 (x D).2).2
  · intro h
    exact absurd (Finset.mem_univ D₀) h

open scoped Classical in
theorem hyperplaneHom_surjective [Finite W] (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A : Subgroup (MulAut W)} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAp : ∀ a ∈ A, a ^ p = 1) {K : Subgroup W} (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K)
    (hfix : fixV A ⊓ K = ⊥) (𝒟 : Finset (Subgroup (MulAut W)))
    (h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p) {k : W} (hk : k ∈ K) :
    k ∈ (hyperplaneHom 𝒟 K).range := by
  classical
  by_cases hA : A = ⊥
  · have h1 : K = ⊥ := by
      rw [hA, fixV_bot] at hfix
      simpa using hfix
    rw [h1, Subgroup.mem_bot] at hk
    rw [hk]
    exact (hyperplaneHom 𝒟 K).range.one_mem
  · have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA
    have : CFSG.IsElementaryAbelian p A :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by simpa using hAp x x.2) }
    let _ : MulDistribMulAction A K := MulDistribMulAction.compHom K (actOnSub hKA)
    obtain ⟨m, hm⟩ := card_eq_two_pow_W hW K
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hm]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).1
        ((Fact.out : Nat.Prime p).dvd_of_dvd_pow h)
      exact hp2 this
    have hgen := CFSG.SolvableHall.abelian_hyperplane_generation (p := p) (A := A) (H := K) hpK
    have hle : ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B K ≤
        (hyperplaneHom 𝒟 K).range.subgroupOf K := by
      refine iSup₂_le fun B hB => ?_
      have hDA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
      have hDrel : (B.map A.subtype).relIndex A = p := by
        have h : (B.map A.subtype).subgroupOf A = B :=
          Subgroup.comap_map_eq_self_of_injective A.subtype_injective B
        rw [Subgroup.relIndex, h]
        exact hB
      have hD𝒟 : B.map A.subtype ∈ 𝒟 := (h𝒟 _).2 ⟨hDA, hDrel⟩
      intro w hw
      have hwD : (w : W) ∈ fixV (B.map A.subtype) := by
        rw [mem_fixV]
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
        exact congrArg Subtype.val (hw ⟨b, hb⟩)
      have hwDK : (w : W) ∈ fixV (B.map A.subtype) ⊓ K := Subgroup.mem_inf.2 ⟨hwD, w.2⟩
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
      refine ⟨Pi.mulSingle (⟨B.map A.subtype, hD𝒟⟩ : 𝒟) ⟨w, hwDK⟩, ?_⟩
      rw [hyperplaneHom_apply, Finset.prod_eq_single (⟨B.map A.subtype, hD𝒟⟩ : 𝒟)]
      · simp
      · intro D _ hD
        rw [Pi.mulSingle_eq_of_ne hD]
        rfl
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hk' : (⟨k, hk⟩ : K) ∈ (hyperplaneHom 𝒟 K).range.subgroupOf K := by
      apply hle
      rw [hgen]
      exact Subgroup.mem_top _
    exact hk'

@[expose] noncomputable def hyperplaneEquiv [Finite W] (hW : ∀ w : W, w * w = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (MulAut W)}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1) {K : Subgroup W}
    (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K) (hfix : fixV A ⊓ K = ⊥)
    (𝒟 : Finset (Subgroup (MulAut W)))
    (h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p) :
    (∀ D : 𝒟, ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) ≃* ↥K :=
  MulEquiv.ofBijective ((hyperplaneHom 𝒟 K).codRestrict K (hyperplaneHom_mem 𝒟 K))
    ⟨fun x y h => hyperplaneHom_injective hW hp2 hAc hAp hKA hfix 𝒟 h𝒟
        (congrArg Subtype.val h),
     fun k => by
      obtain ⟨x, hx⟩ := hyperplaneHom_surjective hW hp2 hAc hAp hKA hfix 𝒟 h𝒟 k.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem hyperplaneEquiv_apply [Finite W] (hW : ∀ w : W, w * w = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (MulAut W)}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1) {K : Subgroup W}
    (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K) (hfix : fixV A ⊓ K = ⊥)
    (𝒟 : Finset (Subgroup (MulAut W)))
    (h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p)
    (x : ∀ D : 𝒟, ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) :
    ((hyperplaneEquiv hW hp2 hAc hAp hKA hfix 𝒟 h𝒟 x : K) : W) =
      ∏ D : 𝒟, ((x D : ↥(fixV (D : Subgroup (MulAut W)) ⊓ K)) : W) :=
  hyperplaneHom_apply 𝒟 K x

open scoped Classical in
theorem card_eq_prod_card_fixV_inf_hyperplanes [Finite W] (hW : ∀ w : W, w * w = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (MulAut W)}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1) {K : Subgroup W}
    (hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K) (hfix : fixV A ⊓ K = ⊥)
    (𝒟 : Finset (Subgroup (MulAut W)))
    (h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p) :
    Nat.card K = ∏ D ∈ 𝒟, Nat.card ↥(fixV D ⊓ K) := by
  have e := Nat.card_congr (hyperplaneEquiv hW hp2 hAc hAp hKA hfix 𝒟 h𝒟).toEquiv
  rw [← e, Nat.card_pi, Finset.prod_coe_sort 𝒟 (fun D => Nat.card ↥(fixV D ⊓ K))]

end Hyperplane


section Orbit

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_fixfree (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    {M : Subgroup W} {σ : MulAut W} (hσM : ∀ m ∈ M, σ m ∈ M) (hσp : ∀ m ∈ M, (σ ^ p) m = m)
    (hfix : ∀ m ∈ M, σ m = m → m = 1) (hM : M ≠ ⊥) :
    2 ^ orderOf (2 : ZMod p) ≤ Nat.card M := by
  let f : M → M := fun a => ⟨σ a, hσM a a.2⟩
  have hiter : ∀ (n : ℕ) (a : M), ((f^[n] a : M) : W) = (σ ^ n) a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]
  have hf : ∀ a, f^[p] a = a := fun a => Subtype.ext (by rw [hiter]; exact hσp a a.2)
  have hmod := card_modEq_fix_prime p f hf
  have hfixcard : Nat.card {a | f a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (map_one σ)⟩⟩⟩
    have hone : ∀ c : {a | f a = a}, (c.1 : W) = 1 := fun c =>
      hfix c.1 c.1.2 (congrArg Subtype.val c.2)
    apply Subtype.ext
    apply Subtype.ext
    rw [hone a, hone b]
  rw [hfixcard] at hmod
  obtain ⟨m, hm⟩ := card_eq_two_pow_W hW M
  have hne : m ≠ 0 := by
    intro hm0
    apply hM
    have h1 : Nat.card M = 1 := by rw [hm, hm0, pow_zero]
    exact Subgroup.card_eq_one.1 h1
  rw [hm] at hmod
  have h2 : ((2 ^ m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  have h3 : orderOf (2 : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one h2
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h3)

theorem eq_of_le_of_relIndex_prime {p : ℕ} [Fact p.Prime] {U D E : Subgroup (MulAut W)}
    (hDE : D ≤ E) (hEU : E ≤ U) (hD : D.relIndex U = p) (hne : D ≠ E) : E = U := by
  have hpD : p * Nat.card D = Nat.card U := by
    have := D.relIndex_mul_card U
    rwa [hD, inf_eq_left.2 (hDE.trans hEU)] at this
  have h1 : Nat.card D ∣ Nat.card E := Subgroup.card_dvd_of_le hDE
  have h2 : Nat.card E ∣ Nat.card U := Subgroup.card_dvd_of_le hEU
  obtain ⟨c, hc⟩ := h1
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hcp : c ∣ p := by
    rw [hc, ← hpD, mul_comm p] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hDpos h2
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 hcp with h | h
  · exfalso
    rw [h, mul_one] at hc
    exact hne (Subgroup.eq_of_le_of_card_ge hDE hc.le)
  · rw [h] at hc
    exact Subgroup.eq_of_le_of_card_ge hEU (by rw [hc, ← hpD, mul_comm])

theorem two_pow_le_card_fixV_inf (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    {U D : Subgroup (MulAut W)} {K : Subgroup W}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUp : ∀ a ∈ U, a ^ p = 1)
    (hKU : ∀ a ∈ U, ∀ k ∈ K, a k ∈ K) (hfix : fixV U ⊓ K = ⊥)
    (hDU : D ≤ U) (hD : D.relIndex U = p) (hne : fixV D ⊓ K ≠ ⊥) :
    2 ^ orderOf (2 : ZMod p) ≤ Nat.card ↥(fixV D ⊓ K) := by
  obtain ⟨u, huU, huD⟩ : ∃ u ∈ U, u ∉ D := by
    by_contra hcon
    push Not at hcon
    have : D = U := le_antisymm hDU hcon
    rw [this, Subgroup.relIndex_self] at hD
    exact (Fact.out : Nat.Prime p).one_lt.ne hD
  have hsup : D ⊔ Subgroup.zpowers u = U := by
    refine eq_of_le_of_relIndex_prime le_sup_left
      (sup_le hDU (Subgroup.zpowers_le.2 huU)) hD ?_
    intro h
    apply huD
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  refine two_pow_le_card_of_fixfree hW (σ := u) ?_ ?_ ?_ hne
  · intro m hm
    obtain ⟨hmD, hmK⟩ := Subgroup.mem_inf.1 hm
    refine Subgroup.mem_inf.2 ⟨?_, hKU u huU m hmK⟩
    rw [mem_fixV]
    intro d hd
    have hcomm : d * u = u * d := hUc d (hDU hd) u huU
    have := congrArg (fun g : MulAut W => g m) hcomm
    simp only [MulAut.mul_apply] at this
    rw [this, mem_fixV.1 hmD d hd]
  · intro m _
    rw [hUp u huU]
    rfl
  · intro m hm hum
    obtain ⟨hmD, hmK⟩ := Subgroup.mem_inf.1 hm
    have hs : Subgroup.zpowers u ≤ MulAction.stabilizer (MulAut W) m :=
      Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hum)
    have hmu : m ∈ fixV (Subgroup.zpowers u) := by
      rw [mem_fixV]
      intro x hx
      have := hs hx
      rwa [MulAction.mem_stabilizer_iff] at this
    have hmU : m ∈ fixV U := by
      rw [← hsup, fixV_sup]
      exact Subgroup.mem_inf.2 ⟨hmD, hmu⟩
    have : m ∈ fixV U ⊓ K := Subgroup.mem_inf.2 ⟨hmU, hmK⟩
    rw [hfix, Subgroup.mem_bot] at this
    exact this

end Orbit

section Conj

variable {G : Type*} [Group G]

@[expose] def conjSub (t : G) (D : Subgroup G) : Subgroup G :=
  D.map (MulAut.conj t).toMonoidHom

theorem mem_conjSub {t : G} {D : Subgroup G} {x : G} :
    x ∈ conjSub t D ↔ t⁻¹ * x * t ∈ D := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem card_conjSub (t : G) (D : Subgroup G) : Nat.card (conjSub t D) = Nat.card D :=
  Subgroup.card_map_of_injective (fun _ _ h => (MulAut.conj t).injective h)

theorem relIndex_le_card_of_conj {T D₀ : Subgroup G} {S : Finset (Subgroup G)}
    (hS : ∀ t ∈ T, conjSub t D₀ ∈ S) :
    (T ⊓ Subgroup.normalizer (D₀ : Set G)).relIndex T ≤ S.card := by
  classical
  let f : ↥T → S := fun t => ⟨conjSub (t : G) D₀, hS t t.2⟩
  let H' : Subgroup ↥T := (T ⊓ Subgroup.normalizer (D₀ : Set G)).subgroupOf T
  let g : (↥T ⧸ H') → S := fun q => f q.out
  have hg : Function.Injective g := by
    intro q1 q2 h
    have h' : conjSub ((q1.out : T) : G) D₀ = conjSub ((q2.out : T) : G) D₀ := congrArg Subtype.val h
    have key : ∀ x : G, ((q1.out : T) : G)⁻¹ * x * ((q1.out : T) : G) ∈ D₀ ↔
        ((q2.out : T) : G)⁻¹ * x * ((q2.out : T) : G) ∈ D₀ := fun x => by
      rw [← mem_conjSub, ← mem_conjSub, h']
    have hmem : (q1.out)⁻¹ * q2.out ∈ H' := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.2 ⟨((q1.out)⁻¹ * q2.out).2, ?_⟩
      rw [Subgroup.mem_set_normalizer_iff]
      intro h0
      have := key (((q2.out : T) : G) * h0 * ((q2.out : T) : G)⁻¹)
      have e1 : ((q1.out : T) : G)⁻¹ * (((q2.out : T) : G) * h0 * ((q2.out : T) : G)⁻¹) *
          ((q1.out : T) : G) = ((((q1.out)⁻¹ * q2.out : T)) : G) * h0 *
          ((((q1.out)⁻¹ * q2.out : T)) : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
        group
      have e2 : ((q2.out : T) : G)⁻¹ * (((q2.out : T) : G) * h0 * ((q2.out : T) : G)⁻¹) *
          ((q2.out : T) : G) = h0 := by group
      rw [e1, e2] at this
      exact this.symm
    have : (QuotientGroup.mk q1.out : T ⧸ H') = QuotientGroup.mk q2.out :=
      QuotientGroup.eq.2 hmem
    simpa using this
  calc (T ⊓ Subgroup.normalizer (D₀ : Set G)).relIndex T = Nat.card (↥T ⧸ H') := by
        rw [Subgroup.relIndex, Subgroup.index_eq_card]
    _ ≤ Nat.card S := Nat.card_le_card_of_injective g hg
    _ = S.card := by simp

end Conj

section Main

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

open scoped Classical in
theorem two_pow_le_card_ker_of_hyperplane_orbit (hW : ∀ w : W, w * w = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {U T : Subgroup (MulAut W)}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUp : ∀ a ∈ U, a ^ p = 1) (hU : U ≠ ⊥)
    (hTU : T ≤ Subgroup.normalizer (U : Set (MulAut W))) {m : ℕ}
    (horb : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      m ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card (normHom U).ker := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hUodd : Odd (Nat.card U) := odd_card_of_pow_eq_one hodd hUp
  set K : Subgroup W := (normHom U).ker with hK
  have hKU : ∀ a ∈ U, ∀ k ∈ K, a k ∈ K := fun a ha k hk =>
    map_ker_normHom (Subgroup.le_normalizer ha) hk
  have hKT : ∀ t ∈ T, ∀ k ∈ K, t k ∈ K := fun t ht k hk => map_ker_normHom (hTU ht) hk
  have hfix : fixV U ⊓ K = ⊥ := fixV_inf_ker_normHom hW hUodd
  have : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    Finset.univ.filter (fun D => D ≤ U ∧ D.relIndex U = p)
  have h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ U ∧ D.relIndex U = p := fun D => by simp [𝒟]
  have hKne : K ≠ ⊥ := by
    intro hK0
    have hcard := card_ker_normHom_mul hW hUodd
    rw [← hK, hK0, Subgroup.card_bot, mul_one] at hcard
    have hfixtop : fixV U = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
    obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU
    apply hu1
    apply Subtype.ext
    apply DFunLike.ext
    intro w
    have : w ∈ fixV U := by rw [hfixtop]; exact Subgroup.mem_top w
    exact mem_fixV.1 this u huU
  have hcardK := card_eq_prod_card_fixV_inf_hyperplanes hW hp2 hUc hUp hKU hfix 𝒟 h𝒟
  obtain ⟨D₀, hD₀𝒟, hD₀ne⟩ : ∃ D ∈ 𝒟, fixV D ⊓ K ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hKne
    apply Subgroup.card_eq_one.1
    rw [hcardK]
    refine Finset.prod_eq_one fun D hD => ?_
    rw [hcon D hD, Subgroup.card_bot]
  obtain ⟨hD₀U, hD₀rel⟩ := (h𝒟 D₀).1 hD₀𝒟
  let 𝒟g : Finset (Subgroup (MulAut W)) := 𝒟.filter (fun D => fixV D ⊓ K ≠ ⊥)
  have hD₀cardpos : 0 < Nat.card D₀ := Nat.card_pos
  have hpD₀ : p * Nat.card D₀ = Nat.card U := by
    have := D₀.relIndex_mul_card U
    rwa [hD₀rel, inf_eq_left.2 hD₀U] at this
  have hconj : ∀ t ∈ T, conjSub t D₀ ∈ 𝒟g := by
    intro t ht
    have htN := hTU ht
    have hle : conjSub t D₀ ≤ U := by
      intro x hx
      rw [mem_conjSub] at hx
      have h1 := hD₀U hx
      have := (Subgroup.mem_set_normalizer_iff.1 htN (t⁻¹ * x * t)).1 h1
      have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rwa [e] at this
    have hrel : (conjSub t D₀).relIndex U = p := by
      have h1 := (conjSub t D₀).relIndex_mul_card U
      rw [inf_eq_left.2 hle, card_conjSub] at h1
      exact Nat.eq_of_mul_eq_mul_right hD₀cardpos (h1.trans hpD₀.symm)
    refine Finset.mem_filter.2 ⟨(h𝒟 _).2 ⟨hle, hrel⟩, ?_⟩
    obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD₀ne
    obtain ⟨hkD, hkK⟩ := Subgroup.mem_inf.1 hk
    apply Subgroup.ne_bot_iff_exists_ne_one.2
    refine ⟨⟨t k, Subgroup.mem_inf.2 ⟨?_, hKT t ht k hkK⟩⟩, ?_⟩
    · rw [mem_fixV]
      intro x hx
      rw [mem_conjSub] at hx
      have hcomm : x * t = t * (t⁻¹ * x * t) := by group
      have hy : (t⁻¹ * x * t) k = k := mem_fixV.1 hkD _ hx
      calc x (t k) = (x * t) k := rfl
        _ = (t * (t⁻¹ * x * t)) k := by rw [hcomm]
        _ = t ((t⁻¹ * x * t) k) := rfl
        _ = t k := by rw [hy]
    · intro h1
      apply hk1
      have h2 : (t : MulAut W) k = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      show k = 1
      have : (t : MulAut W) k = (t : MulAut W) 1 := by rw [h2, map_one]
      exact (t : MulAut W).injective this
  have hm : m ≤ 𝒟g.card :=
    (horb D₀ hD₀U hD₀rel).trans (relIndex_le_card_of_conj hconj)
  have hfac : ∀ D ∈ 𝒟g, 2 ^ orderOf (2 : ZMod p) ≤ Nat.card ↥(fixV D ⊓ K) := by
    intro D hD
    obtain ⟨hD𝒟, hDne⟩ := Finset.mem_filter.1 hD
    obtain ⟨hDU, hDrel⟩ := (h𝒟 D).1 hD𝒟
    exact two_pow_le_card_fixV_inf hW hUc hUp hKU hfix hDU hDrel hDne
  have hpos : ∀ D ∈ 𝒟, 0 < Nat.card ↥(fixV D ⊓ K) := fun D _ => Nat.card_pos
  calc 2 ^ (m * orderOf (2 : ZMod p)) = (2 ^ orderOf (2 : ZMod p)) ^ m := by
        rw [mul_comm, pow_mul]
    _ ≤ (2 ^ orderOf (2 : ZMod p)) ^ 𝒟g.card :=
        Nat.pow_le_pow_right (Nat.one_le_two_pow) hm
    _ = ∏ _D ∈ 𝒟g, 2 ^ orderOf (2 : ZMod p) := by rw [Finset.prod_const]
    _ ≤ ∏ D ∈ 𝒟g, Nat.card ↥(fixV D ⊓ K) := Finset.prod_le_prod hfac
    _ ≤ (∏ D ∈ 𝒟g, Nat.card ↥(fixV D ⊓ K)) *
          ∏ D ∈ 𝒟.filter (fun D => ¬ (fixV D ⊓ K ≠ ⊥)), Nat.card ↥(fixV D ⊓ K) :=
        Nat.le_mul_of_pos_right _ (Finset.prod_pos fun D hD => hpos D (Finset.mem_filter.1 hD).1)
    _ = ∏ D ∈ 𝒟, Nat.card ↥(fixV D ⊓ K) := Finset.prod_filter_mul_prod_filter_not 𝒟 (fun D => fixV D ⊓ K ≠ ⊥)
        (fun D => Nat.card ↥(fixV D ⊓ K))
    _ = Nat.card K := hcardK.symm

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
