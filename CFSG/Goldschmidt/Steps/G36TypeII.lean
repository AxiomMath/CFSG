module

public import CFSG.Goldschmidt.Steps.G36Basic
import CFSG.Walter.Bender1970.S38.SmallQ
import CFSG.Walter.Bender1970.S38.Types
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Walter

variable {L : Type} [Group L] [Finite L] {A₀ : Subgroup L} {T₀ : Sylow 2 L}

theorem g36Local_of_typeII
    (h : G36Hyp L A₀ T₀) (hII : IsGoldTypeII L) : G36Local L A₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZodd, hL⟩ := hII
  set Z := Subgroup.center L with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have : IsSimpleGroup (L ⧸ Z) := h.quasisimple.2
  have hnab : ∃ a b : L ⧸ Z, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L
      h.quasisimple
  have hB : Bender38Type (L ⧸ Z) :=
    bender38Type_of_isTypeL2_or_isTypeJR hnab (hL.imp (fun h2 => Or.inr h2) id)
  set Vg := (T₀ : Subgroup L) with hVg
  have hTZ : ∀ t ∈ Vg, t ∈ Z → t = 1 := by
    intro t ht htZ
    obtain ⟨k, hk⟩ := h.exists_pow_eq_one ht
    exact eq_one_of_pow_two_pow_eq_one hZodd htZ hk
  have hinj : ∀ s ∈ Vg, ∀ t ∈ Vg, π s = π t → s = t := by
    intro s hs t ht hst
    have hz : s⁻¹ * t ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hst
    have := hTZ _ (Vg.mul_mem (Vg.inv_mem hs) ht) hz
    rw [inv_mul_eq_one] at this
    exact this
  set Tb : Sylow 2 (L ⧸ Z) := T₀.mapSurjective hπs with hTb
  have hTbcoe : (Tb : Subgroup (L ⧸ Z)) = Vg.map π := Sylow.coe_mapSurjective _ _
  have hcardTb : Nat.card (Tb : Subgroup (L ⧸ Z)) = Nat.card Vg := by
    rw [hTbcoe, ← SetLike.coe_sort_coe, Subgroup.coe_map,
      Nat.card_image_of_injOn (fun s hs t ht hst => hinj s hs t ht hst)]
    rfl
  have hcard : Nat.card Vg = 4 ∨ Nat.card Vg = 8 := by
    rw [← hcardTb]
    rcases hL with ⟨p, f, hp, hpodd, hf, -, h8, ⟨e⟩⟩ | hJR
    · left
      set S' : Sylow 2 _ := Tb.mapSurjective (f := e.toMonoidHom) e.surjective with hS'
      have h4 := psl2_sylow_two_card_eq_four (GaloisField p f) (GaloisField.card p f hf.ne')
        hpodd hf h8 S'
      have hS'coe : (S' : Subgroup _) = (Tb : Subgroup (L ⧸ Z)).map e.toMonoidHom :=
        Sylow.coe_mapSurjective _ _
      rw [hS'coe, Subgroup.card_map_of_injective e.injective] at h4
      exact h4
    · exact Or.inr (IsTypeJR.sylow_two_of_nonabelian hJR hnab Tb).2
  have hsq : ∀ t ∈ Vg, t ^ 2 = 1 := by
    intro t ht
    have h1 : π t ^ 2 = 1 := (hB.sylow Tb).1 (π t) (by rw [hTbcoe]; exact ⟨t, ht, rfl⟩)
    apply hTZ _ (Vg.pow_mem ht 2)
    rw [← QuotientGroup.eq_one_iff]
    rw [← map_pow] at h1
    exact h1
  have hcomm : ∀ s ∈ Vg, ∀ t ∈ Vg, s * t = t * s := by
    intro s hs t ht
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq s hs)
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq t ht)
    have h1 : (t * s) * (t * s) = 1 := by rw [← sq]; exact hsq _ (Vg.mul_mem ht hs)
    have h2 : t * s = (t * s)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [mul_inv_rev, hs', ht'] at h2
    exact h2.symm
  have hVab : IsMulCommutative Vg := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have hconjL : ∀ u ∈ Vg, ∀ v ∈ Vg, u ≠ 1 → v ≠ 1 → ∃ g : L, g * u * g⁻¹ = v := by
    intro u hu v hv hu1 hv1
    have hord : ∀ w ∈ Vg, w ≠ 1 → orderOf (π w) = 2 := by
      intro w hw hw1
      apply orderOf_eq_prime
      · rw [← map_pow, hsq w hw, map_one]
      · intro h1
        exact hw1 (hinj w hw 1 Vg.one_mem (by rw [h1, map_one]))
    obtain ⟨c, hc⟩ := isConj_iff.mp (hB.isConj _ _ (hord u hu hu1) (hord v hv hv1))
    obtain ⟨g, rfl⟩ := hπs c
    refine ⟨g, ?_⟩
    set w := g * u * g⁻¹ with hw
    have hz : w⁻¹ * v ∈ Z := by
      rw [← QuotientGroup.eq]
      rw [← map_mul, ← map_inv, ← map_mul] at hc
      exact hc
    have hw2 : w * w = 1 := by
      rw [← sq, hw, conj_pow, hsq u hu, mul_one, mul_inv_cancel]
    have hv2 : v * v = 1 := by rw [← sq]; exact hsq v hv
    have hzc := Subgroup.mem_center_iff.mp hz
    have hz2 : (w⁻¹ * v) ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      calc (w⁻¹ * v) * (w⁻¹ * v) = ((w⁻¹ * v) * w⁻¹) * v := by group
        _ = (w⁻¹ * (w⁻¹ * v)) * v := by rw [← hzc w⁻¹]
        _ = (w * w)⁻¹ * (v * v) := by group
        _ = 1 := by rw [hw2, hv2, inv_one, one_mul]
    have h1 := eq_one_of_pow_two_pow_eq_one hZodd hz hz2
    rw [inv_mul_eq_one] at h1
    exact h1
  obtain ⟨a₀, ha₀A, ha₀Z⟩ : ∃ a ∈ A₀, a ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact h.not_le_center hcon
  have ha₀1 : a₀ ≠ 1 := fun h1 => ha₀Z (h1 ▸ Z.one_mem)
  have hA : A₀ = Vg := by
    apply le_antisymm h.le
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact A₀.one_mem
    obtain ⟨g, hg⟩ := hconjL a₀ (h.le ha₀A) t ht ha₀1 ht1
    have := h.closed a₀ ha₀A g⁻¹ (by rw [inv_inv, hg]; exact ht)
    rwa [inv_inv, hg] at this
  rw [hA]
  let _ : CommGroup Vg := IsMulCommutative.instCommGroup
  set Nr := Subgroup.normalizer (Vg : Set L) with hNr
  set φ : Nr →* MulAut Vg := Vg.normalizerMonoidHom with hφ
  have hφapp : ∀ (n : Nr) (x : Vg), ((φ n x : Vg) : L) = (n : L) * (x : L) * (n : L)⁻¹ :=
    fun _ _ => rfl
  set X : Subgroup (MulAut Vg) := φ.range with hX
  have hker : ∀ m : Nr, φ m = 1 ↔ (m : L) ∈ Subgroup.centralizer (Vg : Set L) := by
    intro m
    constructor
    · intro hm
      have : m ∈ φ.ker := hm
      rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · intro hm
      ext x
      rw [hφapp]
      change (m : L) * x * (m : L)⁻¹ = x
      rw [(Subgroup.mem_centralizer_iff.mp hm x x.2).symm, mul_inv_cancel_right]
  have hXodd : Odd (Nat.card X) := by
    have hVN : Vg ≤ Nr := Subgroup.le_normalizer
    have hkerle : Vg.subgroupOf Nr ≤ φ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker, hker]
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_centralizer_iff.mpr fun w hw => hcomm w hw x hx
    have h1 : φ.ker.index = Nat.card X := Subgroup.index_ker φ
    have h2 : φ.ker.index ∣ (Vg.subgroupOf Nr).index := Subgroup.index_dvd_of_le hkerle
    have h3 : (Vg.subgroupOf Nr).index ∣ Vg.index := Subgroup.relIndex_dvd_index_of_le hVN
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2X
    rw [← h1] at h2X
    exact T₀.not_dvd_index (h2X.trans (h2.trans h3))
  have htrans : ∀ u v : Vg, u ≠ 1 → v ≠ 1 → ∃ n ∈ X, n u = v := by
    intro u v hu hv
    obtain ⟨g, hg⟩ := hconjL u u.2 v v.2 (fun h1 => hu (Subtype.ext h1))
      (fun h1 => hv (Subtype.ext h1))
    have : IsMulCommutative (T₀ : Subgroup L) := hVab
    obtain ⟨n, hn, hneq⟩ := Sylow.conj_eq_normalizer_conj_of_mem T₀ (u : L) g⁻¹ u.2
      (by rw [inv_inv, hg]; exact v.2)
    refine ⟨φ ⟨n⁻¹, Nr.inv_mem hn⟩, ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [hφapp]
    simp only [inv_inv] at hneq ⊢
    rw [← hneq, hg]
  have hV2' : ∀ v : Vg, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hsq v v.2)
  obtain ⟨R, hRX, -, hRcard, hRfree, hRtrans, -⟩ :=
    exists_regular_of_card_eq hV2' hcard hXodd htrans
  have hRp : Nat.card R = 3 ∨ Nat.card R = 7 := by omega
  have hRprime : (Nat.card R).Prime := by rcases hRp with hR | hR <;> rw [hR] <;> norm_num
  have hRcyc : IsCyclic R := isCyclic_of_prime_card (hp := ⟨hRprime⟩) rfl
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := R)
  have hRr : R = Subgroup.zpowers (r : MulAut Vg) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hr ⟨x, hx⟩)
      have hj' : (r : MulAut Vg) ^ j = x := by
        have := congrArg Subtype.val hj
        rwa [Subgroup.coe_zpow] at this
      rw [← hj']
      exact Subgroup.zpow_mem_zpowers _ j
    · exact (Subgroup.zpowers_le).mpr r.2
  have hrord : orderOf (r : MulAut Vg) = Nat.card R := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hr]
  obtain ⟨n₀, hn₀⟩ := hRX r.2
  have hrodd : Odd (orderOf (φ n₀)) := by
    rw [hn₀, hrord]
    rcases hRp with h3 | h7
    · rw [h3]; decide
    · rw [h7]; decide
  obtain ⟨k, hkodd, hkz⟩ := exists_odd_pow n₀
  set y' : Nr := n₀ ^ k with hy'
  have hyR : R = Subgroup.zpowers (φ y') := by rw [hkz φ hrodd, hn₀]; exact hRr
  have hyord : orderOf (φ y') = Nat.card R := by
    rw [← Nat.card_zpowers, ← hyR]
  set y : L := (y' : L) with hy
  have hyN : y ∈ Nr := y'.2
  have hcomm_le : ⁅Vg, Subgroup.zpowers y⁆ ≤ Vg :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((Subgroup.zpowers_le).mpr hyN)
  refine ⟨y, hyN, ?_, ?_, ?_, Or.inl ⟨orderOf (φ y'), ?_, ?_⟩⟩
  · rw [hy, Subgroup.orderOf_coe]
    exact hkodd
  ·
    intro b hb c hc hb1 hc1
    obtain ⟨ρ, hρR, hρ⟩ := hRtrans ⟨b, hcomm_le hb⟩ ⟨c, hcomm_le hc⟩
      (fun h1 => hb1 (congrArg Subtype.val h1)) (fun h1 => hc1 (congrArg Subtype.val h1))
    have hρinv : ρ⁻¹ ∈ Subgroup.zpowers (φ y') := hyR ▸ R.inv_mem hρR
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr hρinv : ρ⁻¹ ∈ Submonoid.powers (φ y'))
    refine ⟨m, ?_⟩
    have hm' : (φ y') ^ m = ρ⁻¹ := hm
    have hρeq : ρ = φ ((y' ^ m)⁻¹) := by rw [map_inv, map_pow, hm', inv_inv]
    have h1 := congrArg Subtype.val hρ
    rw [hρeq, hφapp] at h1
    simpa [hy] using h1
  ·
    intro a ha hay
    by_contra haZ
    have ha1 : a ≠ 1 := fun h1 => haZ (h1 ▸ Z.one_mem)
    have hfix : φ y' ⟨a, ha⟩ = ⟨a, ha⟩ := by
      apply Subtype.ext
      rw [hφapp]
      change y * a * y⁻¹ = a
      rw [← hay, mul_inv_cancel_right]
    have h1 := hRfree (φ y') (hyR ▸ Subgroup.mem_zpowers _) ⟨a, ha⟩ hfix
      (fun h2 => ha1 (congrArg Subtype.val h2))
    rw [h1, Subgroup.zpowers_one_eq_bot] at hyR
    rw [hyR, Subgroup.card_bot] at hRp
    omega
  ·
    have := (hker (y' ^ orderOf (φ y'))).mp (by rw [map_pow, pow_orderOf_eq_one])
    simpa [hy] using this
  ·
    intro z hz hzm
    set z' : Nr := ⟨z, hz⟩ with hz'
    have hνm : (φ z') ^ orderOf (φ y') = 1 := by
      rw [← map_pow]
      exact (hker _).mpr (by simpa [hz'] using hzm)
    have hνR : φ z' ∈ R := by
      by_contra hνR
      have hp : (orderOf (φ y')).Prime := hyord ▸ hRprime
      have : Fact (orderOf (φ y')).Prime := ⟨hp⟩
      have hν1 : φ z' ≠ 1 := fun h1 => hνR (h1 ▸ R.one_mem)
      have hνord : orderOf (φ z') = orderOf (φ y') := orderOf_eq_prime hνm hν1
      have hinf : Subgroup.zpowers (φ z') ⊓ R = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨hx1, hx2⟩
        rw [Subgroup.mem_bot]
        by_contra hx'
        have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers (φ z') := (Subgroup.zpowers_le).mpr hx1
        have hxeq : Subgroup.zpowers x = Subgroup.zpowers (φ z') := by
          apply Subgroup.eq_of_le_of_card_ge hxle
          rw [Nat.card_zpowers, Nat.card_zpowers, hνord]
          have hdvd : orderOf x ∣ orderOf (φ z') := orderOf_dvd_of_mem_zpowers hx1
          rw [hνord] at hdvd
          rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
          · exact absurd (orderOf_eq_one_iff.mp h1) hx'
          · exact h1.ge
        apply hνR
        have : φ z' ∈ Subgroup.zpowers x := hxeq ▸ Subgroup.mem_zpowers _
        exact ((Subgroup.zpowers_le).mpr hx2) this
      have hzX : Subgroup.zpowers (φ z') ≤ X := (Subgroup.zpowers_le).mpr ⟨z', rfl⟩
      have hle := card_mul_card_le_of_inf_eq_bot hzX hRX hinf
      rw [Nat.card_zpowers, hνord, hyord] at hle
      obtain ⟨hA4, hA8⟩ := card_mulAut_of_elementary hV2'
      have hXdvd : Nat.card X ∣ Nat.card (MulAut Vg) := Subgroup.card_subgroup_dvd_card X
      have hcop : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hXodd
      rcases hcard with h4 | h8
      · rw [hA4 h4, show (6 : ℕ) = 2 * 3 from rfl] at hXdvd
        have h3 : Nat.card X ∣ 3 := hcop.dvd_of_dvd_mul_left hXdvd
        have := Nat.le_of_dvd (by norm_num) h3
        have hR3 : Nat.card R = 3 := by omega
        rw [hR3] at hle
        omega
      · rw [hA8 h8, show (168 : ℕ) = 2 ^ 3 * 21 from rfl] at hXdvd
        have h21 : Nat.card X ∣ 21 := (Nat.Coprime.pow_right 3 hcop).dvd_of_dvd_mul_left hXdvd
        have := Nat.le_of_dvd (by norm_num) h21
        have hR7 : Nat.card R = 7 := by omega
        rw [hR7] at hle
        omega
    rw [hyR] at hνR
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hνR
    have hker1 : φ (z' * (y' ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hj, mul_inv_cancel]
    have hcz := (hker _).mp hker1
    have hzeq : z = (z * (y ^ j)⁻¹) * y ^ j := by group
    rw [hzeq]
    refine Subgroup.mul_mem _ (le_sup_right (a := Subgroup.zpowers y) ?_)
      (le_sup_left (b := Subgroup.centralizer (Vg : Set L)) (Subgroup.zpow_mem_zpowers y j))
    simpa [hz', hy] using hcz

end CFSG.Goldschmidt
