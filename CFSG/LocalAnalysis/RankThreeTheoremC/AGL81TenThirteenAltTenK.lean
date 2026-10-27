module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenRho
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenPerm
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAltTen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoAltTen
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
import CFSG.LargeExtraspecial.S5Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoA5Lift
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open CFSG.Open Subgroup Equiv Equiv.Perm
open scoped commutatorElement

theorem pres_iff {B : Finset (Fin 10)} {g : Perm (Fin 10)} (hg : ∀ i ∈ B, g i ∈ B) :
    ∀ x, g x ∈ B ↔ x ∈ B := by
  have himg : B.image g = B := Finset.eq_of_subset_of_card_le
    (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact hg z hz)
    (by rw [Finset.card_image_of_injective _ g.injective])
  intro x
  refine ⟨fun hx => ?_, hg x⟩
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp (himg.symm ▸ hx : g x ∈ B.image g)
  exact g.injective hzx ▸ hz

theorem pow_odd_swap {B : Finset (Fin 10)} {g : Perm (Fin 10)} (hg : ∀ x, g x ∈ B ↔ x ∉ B)
    {m : ℕ} (hm : Odd m) : ∀ x, (g ^ m) x ∈ B ↔ x ∉ B := by
  have h2 : ∀ x, (g ^ 2) x ∈ B ↔ x ∈ B := by
    intro x
    rw [pow_two, Perm.mul_apply, hg, hg, not_not]
  have hev : ∀ r : ℕ, ∀ x, ((g ^ 2) ^ r) x ∈ B ↔ x ∈ B := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      intro x
      rw [pow_succ, Perm.mul_apply, ih, h2]
  obtain ⟨r, rfl⟩ := hm
  intro x
  rw [pow_succ, pow_mul, Perm.mul_apply, hev, hg]

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]

theorem rho_mem_alt_of_odd (eK : ↥K ≃* alternatingGroup (Fin 10)) {y : Y}
    (hy : Odd (orderOf y)) : rho eK y ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]
  have h1 : Perm.sign (rho eK y) ^ orderOf y = 1 := by
    rw [← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign (rho eK y)) with h | h
  · exact h
  · rw [h, hy.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem rho_mem_alt_of_perfect (eK : ↥K ≃* alternatingGroup (Fin 10)) {J : Subgroup Y}
    (hJp : ⁅J, J⁆ = J) : ∀ x ∈ J, rho eK x ∈ alternatingGroup (Fin 10) := by
  have hle : ⁅J, J⁆ ≤ (Perm.sign.comp (rho eK)).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      mul_comm]
  intro x hx
  rw [← hJp] at hx
  exact (MonoidHom.mem_ker.mp (hle hx) : Perm.sign (rho eK x) = 1)

theorem exists_mem_of_rho_mem (eK : ↥K ≃* alternatingGroup (Fin 10)) {y : Y}
    (h : rho eK y ∈ alternatingGroup (Fin 10)) :
    ∃ k : ↥K, eK k = ⟨rho eK y, h⟩ ∧ ((k : Y)⁻¹ * y) ∈ centralizer (K : Set Y) := by
  refine ⟨eK.symm ⟨rho eK y, h⟩, by simp, ?_⟩
  rw [← rho_eq_one_iff eK, map_mul, map_inv, rho_coe, MulEquiv.apply_symm_apply]
  exact inv_mul_cancel _

theorem exists_swap_of_altTen (eK : ↥K ≃* alternatingGroup (Fin 10)) {Y₀ J : Subgroup Y}
    (hcent : centralizer (K : Set Y) ≤ Y₀) (hKY : ¬ K ≤ Y₀) (T : Sylow 5 ↥K)
    (hN : normalizer ((T : Subgroup K) : Set K) ≤ Y₀.subgroupOf K)
    (hF : ∀ s ∈ (T : Subgroup K), s ≠ 1 → ∀ k : ↥K, Commute k s → (k : Y) ∈ Y₀)
    (hJY : J ≤ Y₀) (hJs : IsSubnormal J Y₀) (hJp : ⁅J, J⁆ = J)
    (hJC : ¬ J ≤ centralizer (K : Set Y))
    (hJirr : ∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) :
    ∃ k : ↥K, (k : Y) ∈ Y₀ ∧ (∃ n : ℕ, k ^ 2 ^ n = 1) ∧
      (¬ ∀ x ∈ J, (k : Y) * x * (k : Y)⁻¹ ∈ J) ∧
      ∀ i ∈ J, ¬ ∀ x ∈ J, (k : Y) ^ 2 * x * ((k : Y) ^ 2)⁻¹ = i * x * i⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hes : Function.Surjective eK.toMonoidHom := eK.surjective
  set S : Sylow 5 (alternatingGroup (Fin 10)) := T.mapSurjective hes with hS
  obtain ⟨B, hB, hSB, ⟨g, hgN, hgB⟩, hYB⟩ := RankOneCent.kFactAltTenOvergroup_holds S
  have hgswap : ∀ x, (g : Perm (Fin 10)) x ∈ B ↔ x ∉ B := swap_iff hB hgB
  have hBc : Bᶜ.card = 5 := by rw [Finset.card_compl, hB]; rfl
  set K₁ : Subgroup (alternatingGroup (Fin 10)) := (Y₀.subgroupOf K).map eK.toMonoidHom with hK₁
  have hNS : normalizer ((S : Subgroup (alternatingGroup (Fin 10))) : Set _) ≤ K₁ := by
    rw [show (S : Subgroup (alternatingGroup (Fin 10))) = (T : Subgroup K).map eK.toMonoidHom
      from rfl, ← map_equiv_normalizer_eq]
    exact map_mono hN
  have hK₁t : K₁ ≠ ⊤ := by
    intro h
    apply hKY
    intro x hx
    have hmem : eK ⟨x, hx⟩ ∈ K₁ := h ▸ mem_top _
    obtain ⟨k, hk, hke⟩ := hmem
    have : k = ⟨x, hx⟩ := eK.injective hke
    have h1 := mem_subgroupOf.mp hk
    rw [this] at h1
    exact h1
  have hmemK₁ : ∀ k : ↥K, (k : Y) ∈ Y₀ → eK k ∈ K₁ := fun k hk => ⟨k, hk, rfl⟩
  have hK₁mem : ∀ σ ∈ K₁, ((eK.symm σ : ↥K) : Y) ∈ Y₀ := by
    rintro σ ⟨k, hk, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact mem_subgroupOf.mp hk
  have hpres : ∀ σ ∈ K₁, (∀ x, (σ : Perm (Fin 10)) x ∈ B ↔ x ∈ B) ∨
      (∀ x, (σ : Perm (Fin 10)) x ∈ B ↔ x ∉ B) := by
    intro σ hσ
    rcases hYB K₁ hNS hK₁t σ hσ with h | h
    · exact Or.inl (pres_iff h)
    · exact Or.inr (swap_iff hB h)
  have hJA : ∀ x ∈ J, (rho eK) x ∈ alternatingGroup (Fin 10) := rho_mem_alt_of_perfect eK hJp
  set Jt : Subgroup (alternatingGroup (Fin 10)) := (J.map (rho eK)).comap (alternatingGroup (Fin 10)).subtype with hJt
  have hmemJt : ∀ σ : alternatingGroup (Fin 10), σ ∈ Jt ↔ ∃ x ∈ J, (rho eK) x = σ := by
    intro σ
    rw [hJt, mem_comap, mem_map]
    rfl
  have hJtK₁ : Jt ≤ K₁ := by
    intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := (hmemJt σ).1 hσ
    have hxA : (rho eK) x ∈ alternatingGroup (Fin 10) := hJA x hx
    obtain ⟨k, hk, hkC⟩ := exists_mem_of_rho_mem eK hxA
    have hkY : (k : Y) ∈ Y₀ := by
      have h1 : (k : Y) = x * ((k : Y)⁻¹ * x)⁻¹ := by group
      rw [h1]
      exact Y₀.mul_mem (hJY hx) (Y₀.inv_mem (hcent hkC))
    have : σ = eK k := by
      rw [hk]
      exact Subtype.ext hxσ.symm
    rw [this]
    exact hmemK₁ k hkY
  set ψ : ↥J →* alternatingGroup (Fin 10) :=
    ((rho eK).comp J.subtype).codRestrict (alternatingGroup (Fin 10)) (fun x => hJA x x.2) with hψ
  have hψrange : ψ.range = Jt := by
    ext σ
    rw [MonoidHom.mem_range, hmemJt]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, hxσ⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxσ⟩
  have hJperf : commutator ↥J = ⊤ :=
    ((CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J).mpr
      hJp).commutator_eq_top
  have hJtp : ⁅Jt, Jt⁆ = Jt := by
    rw [← hψrange, MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def, hJperf]
  have hJt1 : Jt ≠ ⊥ := by
    intro h
    apply hJC
    intro x hx
    have h1 : (⟨(rho eK) x, hJA x hx⟩ : alternatingGroup (Fin 10)) ∈ Jt := (hmemJt _).2 ⟨x, hx, rfl⟩
    rw [h, mem_bot] at h1
    exact (rho_eq_one_iff eK x).1 (congrArg Subtype.val h1)
  have hJtirr : ∀ N₁ N₂ : Subgroup Jt, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ →
      N₁ = ⊤ ∨ N₂ = ⊤ := by
    have h := TenFourteenTwo.joinIrreducible_map ψ.rangeRestrict ψ.rangeRestrict_surjective
      hJirr
    rw [hψrange] at h
    exact h
  obtain ⟨eJ⟩ := TenFourteenTwo.nonempty_mulEquiv_alt5_of_altTen (MulEquiv.refl _) S hNS
    hK₁t hJtK₁ hJtp hJt1 hJtirr
  have hJtsub : IsSubnormal Jt K₁ := by
    have h1 := (hJs.map (rho eK)).inf (alternatingGroup (Fin 10))
    have h2 : J.map (rho eK) ⊓ alternatingGroup (Fin 10) = J.map (rho eK) := by
      rw [inf_eq_left]
      rintro _ ⟨x, hx, rfl⟩
      exact hJA x hx
    have h3 : (Y₀.map (rho eK) ⊓ alternatingGroup (Fin 10)).comap (alternatingGroup (Fin 10)).subtype = K₁ := by
      ext σ
      rw [mem_comap, mem_inf, mem_map]
      constructor
      · rintro ⟨⟨y, hy, hyσ⟩, -⟩
        have hyA : (rho eK) y ∈ alternatingGroup (Fin 10) := hyσ ▸ σ.2
        obtain ⟨k, hk, hkC⟩ := exists_mem_of_rho_mem eK hyA
        have hkY : (k : Y) ∈ Y₀ := by
          have h1 : (k : Y) = y * ((k : Y)⁻¹ * y)⁻¹ := by group
          rw [h1]
          exact Y₀.mul_mem hy (Y₀.inv_mem (hcent hkC))
        have : σ = eK k := by
          rw [hk]
          exact Subtype.ext hyσ.symm
        rw [this]
        exact hmemK₁ k hkY
      · rintro ⟨k, hk, rfl⟩
        refine ⟨⟨(k : Y), hk, ?_⟩, (eK k).2⟩
        rw [rho_coe]
        simp
    have h4 := h1.comap (alternatingGroup (Fin 10)).subtype
    rw [h2, h3] at h4
    exact h4
  obtain ⟨s, hsS, hs1, hsB⟩ := exists_fix_of_sylow hB S hSB
  have hAltK₁ : (alternatingGroup.ofSubtype B).range ≤ K₁ := by
    intro σ hσ
    obtain ⟨s₀, hs₀T, rfl⟩ := hsS
    have hs₀1 : s₀ ≠ 1 := fun h => hs1 (by rw [h, map_one])
    have hsupp : Disjoint (σ : Perm (Fin 10)) ((eK s₀ : alternatingGroup (Fin 10)) : Perm (Fin 10)) := by
      rw [Perm.disjoint_iff_disjoint_support]
      rw [alternatingGroup.mem_range_ofSubtype_iff] at hσ
      refine Finset.disjoint_of_subset_left hσ ?_
      rw [Finset.disjoint_left]
      intro x hxB hxs
      exact (Perm.mem_support.mp hxs) (hsB x hxB)
    have hcommA : Commute σ (eK s₀) := by
      show σ * eK s₀ = eK s₀ * σ
      exact Subtype.ext hsupp.commute.eq
    have hcomm : Commute (eK.symm σ) s₀ := by
      have := hcommA.map eK.symm.toMonoidHom
      simpa using this
    have h1 := hF s₀ hs₀T hs₀1 _ hcomm
    have h2 := hmemK₁ _ h1
    rwa [MulEquiv.apply_symm_apply] at h2
  set St : Subgroup (alternatingGroup (Fin 10)) :=
    { carrier := {σ | ∀ x, (σ : Perm (Fin 10)) x ∈ B ↔ x ∈ B}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb x => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul, Perm.mul_apply] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := fun {a} ha x => by
        simp only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢
        rw [← ha, perm_apply_inv] } with hSt
  have hDn : ((K₁ ⊓ St).subgroupOf K₁).Normal := by
    refine ⟨fun d hd k => ?_⟩
    rw [mem_subgroupOf] at hd ⊢
    refine ⟨K₁.mul_mem (K₁.mul_mem k.2 hd.1) (K₁.inv_mem k.2), fun x => ?_⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Perm.mul_apply]
    have hdB := hd.2
    rcases hpres k k.2 with hk | hk
    · have hk' : ∀ x, (k : Perm (Fin 10))⁻¹ x ∈ B ↔ x ∈ B := fun x => by
        have h := hk ((k : Perm (Fin 10))⁻¹ x)
        rw [perm_apply_inv] at h
        exact h.symm
      rw [hk, hdB, hk']
    · have hk' : ∀ x, (k : Perm (Fin 10))⁻¹ x ∈ B ↔ x ∉ B := fun x => by
        have h := hk ((k : Perm (Fin 10))⁻¹ x)
        rw [perm_apply_inv] at h
        constructor
        · intro h1 h2
          exact (h.1 h2) h1
        · intro h1
          by_contra h2
          exact h1 (h.2 h2)
      rw [hk, hdB, hk', not_not]
  have hAltSt : (alternatingGroup.ofSubtype B).range ≤ St := by
    intro σ hσ x
    rw [alternatingGroup.mem_range_ofSubtype_iff] at hσ
    by_cases hx : (σ : Perm (Fin 10)) x = x
    · rw [hx]
    · have h1 : x ∈ B := hσ (Perm.mem_support.mpr hx)
      have h2 : (σ : Perm (Fin 10)) x ∈ B := hσ (Perm.apply_mem_support.mpr (Perm.mem_support.mpr hx))
      exact ⟨fun _ => h1, fun _ => h2⟩
  have hAltn : (((alternatingGroup.ofSubtype B).range).subgroupOf (K₁ ⊓ St)).Normal := by
    refine ⟨fun σ hσ d => ?_⟩
    rw [mem_subgroupOf] at hσ ⊢
    rw [alternatingGroup.mem_range_ofSubtype_iff] at hσ ⊢
    intro x hx
    have hdB := (d.2 : (d : alternatingGroup (Fin 10)) ∈ K₁ ⊓ St).2
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hx
    rw [Perm.mem_support] at hx
    by_contra hxB
    apply hx
    have h1 : ¬ ((d : alternatingGroup (Fin 10)) : Perm (Fin 10))⁻¹ x ∈ B := by
      rw [← hdB, perm_apply_inv]
      exact hxB
    have h2 : (σ : Perm (Fin 10)) (((d : alternatingGroup (Fin 10)) : Perm (Fin 10))⁻¹ x) =
        ((d : alternatingGroup (Fin 10)) : Perm (Fin 10))⁻¹ x := by
      by_contra hne
      exact h1 (hσ (Perm.mem_support.mpr hne))
    rw [Perm.mul_apply, Perm.mul_apply, h2, perm_apply_inv]
  have hAltsub : IsSubnormal (alternatingGroup.ofSubtype B).range K₁ :=
    IsSubnormal.step (le_inf hAltK₁ hAltSt) hAltn
      (IsSubnormal.step inf_le_left hDn (IsSubnormal.refl K₁))
  obtain ⟨eB⟩ := CFSG.LocalAnalysis.GLTheoremA.AltDown.nonempty_range_ofSubtype_equiv B 5 hB
  have hcJ : IsComponentOf Jt K₁ := ⟨hJtK₁, hJtsub, isQuasisimple_of_equiv_alt5 eJ⟩
  have hcB : IsComponentOf (alternatingGroup.ofSubtype B).range K₁ :=
    ⟨hAltK₁, hAltsub, isQuasisimple_of_equiv_alt5 eB⟩
  have hcard : Nat.card Jt = 60 := by
    rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hJcase : Jt = (alternatingGroup.ofSubtype B).range ∨
      Jt = (alternatingGroup.ofSubtype Bᶜ).range := by
    by_cases heq : Jt = (alternatingGroup.ofSubtype B).range
    · exact Or.inl heq
    · right
      have hc := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hcJ hcB heq
      have hle : Jt ≤ (alternatingGroup.ofSubtype Bᶜ).range := by
        intro x hx
        rw [alternatingGroup.mem_range_ofSubtype_iff]
        have hfix := fix_of_commute_range hB (c := (x : Perm (Fin 10))) (fun σ hσ => by
          have h1 : ⁅x, σ⁆ = 1 := by
            have := Subgroup.commutator_mem_commutator hx hσ
            rw [hc, mem_bot] at this
            exact this
          have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
          exact congrArg Subtype.val h2)
        intro y hy
        rw [Finset.mem_compl]
        intro hyB
        exact (Perm.mem_support.mp hy) (hfix y hyB)
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_altB hBc, hcard])
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set g₂ := g ^ m with hg₂
  have hg₂swap : ∀ x, (g₂ : Perm (Fin 10)) x ∈ B ↔ x ∉ B := by
    rw [hg₂, SubgroupClass.coe_pow]
    exact pow_odd_swap hgswap hm
  have hg₂K₁ : g₂ ∈ K₁ := K₁.pow_mem (hNS hgN) m
  have hg₂pow : g₂ ^ 2 ^ a = 1 := by
    rw [hg₂, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  refine ⟨eK.symm g₂, hK₁mem g₂ hg₂K₁, ⟨a, by rw [← map_pow, hg₂pow, map_one]⟩, ?_, ?_⟩
  ·
    intro hnorm
    have hρk : (rho eK) ((eK.symm g₂ : ↥K) : Y) = (g₂ : Perm (Fin 10)) := by
      rw [rho_coe, MulEquiv.apply_symm_apply]
    obtain ⟨⟨σ, hσJ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJt1
    obtain ⟨x, hx, hxσ⟩ := (hmemJt σ).1 hσJ
    have hconjEq : (rho eK) (((eK.symm g₂ : ↥K) : Y) * x * ((eK.symm g₂ : ↥K) : Y)⁻¹) =
        (g₂ : Perm (Fin 10)) * (rho eK) x * (g₂ : Perm (Fin 10))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hρk]
    have hconj : (⟨(rho eK) (((eK.symm g₂ : ↥K) : Y) * x * ((eK.symm g₂ : ↥K) : Y)⁻¹),
        hJA _ (hnorm x hx)⟩ : alternatingGroup (Fin 10)) ∈ Jt :=
      (hmemJt _).2 ⟨_, hnorm x hx, rfl⟩
    have hσ1' : (σ : Perm (Fin 10)) ≠ 1 := fun h => hσ1 (Subtype.ext (Subtype.ext h))
    obtain ⟨y, hy⟩ : ∃ y, (σ : Perm (Fin 10)) y ≠ y := by
      by_contra h
      push Not at h
      exact hσ1' (Equiv.ext h)
    rw [← hxσ] at hy
    rcases hJcase with hJB | hJB
    ·
      have hσB : (⟨(rho eK) x, hJA x hx⟩ : alternatingGroup (Fin 10)) ∈
          (alternatingGroup.ofSubtype B).range := hJB ▸ (hmemJt _).2 ⟨x, hx, rfl⟩
      rw [alternatingGroup.mem_range_ofSubtype_iff] at hσB
      have hyB : y ∈ B := hσB (Perm.mem_support.mpr hy)
      have hc := hJB ▸ hconj
      rw [alternatingGroup.mem_range_ofSubtype_iff] at hc
      have hgy : (g₂ : Perm (Fin 10)) y ∉ B := fun h => ((hg₂swap y).1 h) hyB
      apply hgy
      apply hc
      rw [Perm.mem_support]
      change (rho eK) (((eK.symm g₂ : ↥K) : Y) * x * ((eK.symm g₂ : ↥K) : Y)⁻¹) _ ≠ _
      rw [hconjEq]
      simp only [Perm.mul_apply, perm_inv_apply]
      intro h
      exact hy ((g₂ : Perm (Fin 10)).injective h)
    · have hσB : (⟨(rho eK) x, hJA x hx⟩ : alternatingGroup (Fin 10)) ∈
          (alternatingGroup.ofSubtype Bᶜ).range := hJB ▸ (hmemJt _).2 ⟨x, hx, rfl⟩
      rw [alternatingGroup.mem_range_ofSubtype_iff] at hσB
      have hyB : y ∉ B := Finset.mem_compl.mp (hσB (Perm.mem_support.mpr hy))
      have hc := hJB ▸ hconj
      rw [alternatingGroup.mem_range_ofSubtype_iff] at hc
      have hgy : (g₂ : Perm (Fin 10)) y ∈ B := (hg₂swap y).2 hyB
      apply Finset.mem_compl.mp (hc ?_) hgy
      rw [Perm.mem_support]
      change (rho eK) (((eK.symm g₂ : ↥K) : Y) * x * ((eK.symm g₂ : ↥K) : Y)⁻¹) _ ≠ _
      rw [hconjEq]
      simp only [Perm.mul_apply, perm_inv_apply]
      intro h
      exact hy ((g₂ : Perm (Fin 10)).injective h)
  ·
    intro i hi hinner
    have hρk : (rho eK) ((eK.symm g₂ : ↥K) : Y) = (g₂ : Perm (Fin 10)) := by
      rw [rho_coe, MulEquiv.apply_symm_apply]
    set c : Perm (Fin 10) := ((rho eK) i)⁻¹ * (g₂ : Perm (Fin 10)) ^ 2 with hc
    have hcomm : ∀ σ ∈ Jt, Commute c (σ : Perm (Fin 10)) := by
      intro σ hσ
      obtain ⟨x, hx, hxσ⟩ := (hmemJt σ).1 hσ
      have h1 := congrArg (rho eK) (hinner x hx)
      simp only [map_mul, map_inv, map_pow, hρk] at h1
      rw [← hxσ]
      show c * (rho eK) x = (rho eK) x * c
      rw [hc]
      calc ((rho eK) i)⁻¹ * (g₂ : Perm (Fin 10)) ^ 2 * (rho eK) x
          = ((rho eK) i)⁻¹ * ((g₂ : Perm (Fin 10)) ^ 2 * (rho eK) x * ((g₂ : Perm (Fin 10)) ^ 2)⁻¹) *
              (g₂ : Perm (Fin 10)) ^ 2 := by group
        _ = ((rho eK) i)⁻¹ * ((rho eK) i * (rho eK) x * ((rho eK) i)⁻¹) * (g₂ : Perm (Fin 10)) ^ 2 := by rw [h1]
        _ = (rho eK) x * (((rho eK) i)⁻¹ * (g₂ : Perm (Fin 10)) ^ 2) := by group
    have hiJt : (⟨(rho eK) i, hJA i hi⟩ : alternatingGroup (Fin 10)) ∈ Jt := (hmemJt _).2 ⟨i, hi, rfl⟩
    have hsg₂ : Perm.sign (g₂ : Perm (Fin 10)) = 1 := (g₂ : alternatingGroup (Fin 10)).2
    have hsi : Perm.sign ((rho eK) i) = 1 := hJA i hi
    have hsq : (g₂ : Perm (Fin 10)) ^ 2 = (rho eK) i * c := by rw [hc, ← mul_assoc, mul_inv_cancel, one_mul]
    rcases hJcase with hJB | hJB
    · have hcB := fix_of_commute_range hB (c := c) (fun σ hσ => hcomm σ (hJB ▸ hσ))
      have hiB := hJB ▸ hiJt
      rw [alternatingGroup.mem_range_ofSubtype_iff] at hiB
      have hiBc : ∀ x, x ∉ B → (rho eK) i x = x := fun x hx => by
        by_contra hne
        exact hx (hiB (Perm.mem_support.mpr hne))
      exact false_of_sq_eq_mul hg₂swap hsg₂ hiBc hsi hcB hsq
    · have hcB := fix_of_commute_range hBc (c := c) (fun σ hσ => hcomm σ (hJB ▸ hσ))
      have hiB := hJB ▸ hiJt
      rw [alternatingGroup.mem_range_ofSubtype_iff] at hiB
      have hiBc : ∀ x, x ∉ Bᶜ → (rho eK) i x = x := fun x hx => by
        by_contra hne
        exact hx (hiB (Perm.mem_support.mpr hne))
      have hswap' : ∀ x, (g₂ : Perm (Fin 10)) x ∈ Bᶜ ↔ x ∉ Bᶜ := fun x => by
        rw [Finset.mem_compl, Finset.mem_compl, not_not, hg₂swap, not_not]
      exact false_of_sq_eq_mul hswap' hsg₂ hiBc hsi hcB hsq

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
