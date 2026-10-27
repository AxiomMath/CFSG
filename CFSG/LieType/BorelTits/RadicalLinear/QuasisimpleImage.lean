module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem exists_map_eq_of_isQuasisimple {I : Type*} {Y : I → Type*} [∀ i, Group (Y i)]
    (Ψ : ∀ i, X →* Y i) (J : ∀ i, Subgroup (Y i)) (good : I → Prop)
    (hcomm : ∀ x y : X, (∀ i, Ψ i x = 1) → (∀ i, Ψ i y = 1) → x * y = y * x)
    (hbad : ∀ i, ¬ good i → IsSolvable (Ψ i).range)
    (hsimple : ∀ i, good i → IsSimpleGroup (J i))
    (hle : ∀ i, good i → J i ≤ (Ψ i).range)
    (hcommJ : ∀ i, good i → commutator (Y i) ≤ J i)
    {S : Subgroup X} (hSn : S.Normal) (hS : CFSG.IsQuasisimple S) :
    ∃ i, good i ∧ S.map (Ψ i) = J i ∧ (Ψ i).ker.subgroupOf S ≤ Subgroup.center S := by
  classical
  have hperfS : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp hS.1
  have hperfMap : ∀ i, ⁅S.map (Ψ i), S.map (Ψ i)⁆ = S.map (Ψ i) := by
    intro i
    rw [← Subgroup.map_commutator, hperfS]
  have hbot : ∀ i, ¬ good i → S.map (Ψ i) = ⊥ := by
    intro i hi
    haveI : Group.IsSolvable ↥((Ψ i).range) := hbad i hi
    have key : ∀ H : Subgroup ↥((Ψ i).range), ⁅H, H⁆ = H → H = ⊥ := by
      intro H hH
      haveI : Group.IsSolvable H := inferInstance
      haveI : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
      by_contra hne
      haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne
        (Group.IsPerfect.commutator_eq_top (G := H))
    set φ : X →* ↥((Ψ i).range) :=
      (Ψ i).codRestrict (Ψ i).range (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩) with hφ
    have hperfφ : ⁅S.map φ, S.map φ⁆ = S.map φ := by
      rw [← Subgroup.map_commutator, hperfS]
    have hker : φ.ker = (Ψ i).ker := by
      rw [hφ]
      exact MonoidHom.ker_codRestrict _ _ _
    have hbotφ : S.map φ = ⊥ := key (S.map φ) hperfφ
    rwa [Subgroup.map_eq_bot_iff, hker, ← Subgroup.map_eq_bot_iff] at hbotφ
  have hgood : ∀ i, good i → S.map (Ψ i) = ⊥ ∨ S.map (Ψ i) = J i := by
    intro i hi
    haveI : IsSimpleGroup ↥(J i) := hsimple i hi
    have hleR : S.map (Ψ i) ≤ (Ψ i).range := Subgroup.map_le_range (Ψ i) S
    have hleJ : S.map (Ψ i) ≤ J i := by
      rw [← hperfMap i]
      calc ⁅S.map (Ψ i), S.map (Ψ i)⁆ ≤ ⁅(Ψ i).range, (Ψ i).range⁆ :=
            Subgroup.commutator_mono hleR hleR
        _ ≤ ⁅(⊤ : Subgroup (Y i)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator (Y i) := (commutator_def (Y i)).symm
        _ ≤ J i := hcommJ i hi
    have hN : ((S.map (Ψ i)).subgroupOf (J i)).Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn g
      have hn' : (n : Y i) ∈ S.map (Ψ i) := hn
      obtain ⟨s, hs, hsn⟩ := Subgroup.mem_map.mp hn'
      obtain ⟨x, hx⟩ := hle i hi (g : J i).2
      rw [Subgroup.mem_subgroupOf]
      show (g : Y i) * (n : Y i) * (g : Y i)⁻¹ ∈ S.map (Ψ i)
      rw [← hx, ← hsn, ← map_inv, ← map_mul, ← map_mul]
      exact Subgroup.mem_map_of_mem (Ψ i) (Subgroup.Normal.conj_mem hSn s hs x)
    rcases hN.eq_bot_or_eq_top with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hleJ hx⟩ : ↥(J i)) ∈ (S.map (Ψ i)).subgroupOf (J i) := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      rw [h] at hx'
      have h1 : (⟨x, hleJ hx⟩ : ↥(J i)) = 1 := Subgroup.mem_bot.mp hx'
      simpa using congrArg Subtype.val h1
    · right
      rw [Subgroup.subgroupOf_eq_top] at h
      exact le_antisymm hleJ h
  have hex : ∃ i, good i ∧ S.map (Ψ i) = J i := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hall : ∀ i, S.map (Ψ i) = ⊥ := by
      intro i
      by_cases hi : good i
      · rcases hgood i hi with h | h
        · exact h
        · exact absurd h (hcon i hi)
      · exact hbot i hi
    have hzero : ∀ i (x : S), Ψ i (x : X) = 1 := by
      intro i x
      have hmem : Ψ i (x : X) ∈ S.map (Ψ i) := Subgroup.mem_map_of_mem (Ψ i) x.2
      rw [hall i] at hmem
      simpa using hmem
    have hcenter : Subgroup.center S = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm (x : X) (y : X) (hzero · x) (hzero · y)).symm
    have hsub : Subsingleton (S ⧸ Subgroup.center S) := by
      rw [hcenter]
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup ↥S) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup ↥S) b
      have hx : QuotientGroup.mk' (⊤ : Subgroup ↥S) x = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact Subgroup.mem_top x
      have hy : QuotientGroup.mk' (⊤ : Subgroup ↥S) y = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact Subgroup.mem_top y
      rw [hx, hy]
    obtain ⟨a, b, hab⟩ := hS.2.2
    exact hab (by rw [hsub.allEq a b])
  obtain ⟨i, hi, hJi⟩ := hex
  refine ⟨i, hi, hJi, ?_⟩
  haveI : IsSimpleGroup ↥(J i) := hsimple i hi
  haveI : Nontrivial ↥(J i) := inferInstance
  set ψ : ↥S →* ↥(J i) :=
    ((Ψ i).domRestrict S).codRestrict (J i)
      (fun x => by rw [← hJi]; exact Subgroup.mem_map_of_mem (Ψ i) x.2) with hψ
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : Y i) ∈ S.map (Ψ i) := by rw [hJi]; exact y.2
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
  have hkereq : ψ.ker = (Ψ i).ker.subgroupOf S := by
    rw [hψ, MonoidHom.ker_codRestrict, MonoidHom.ker_restrict]
  obtain ⟨hperf, hsimp, -⟩ := hS
  have hNbar : (ψ.ker.map (QuotientGroup.mk' (Subgroup.center S))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hNbar.eq_bot_or_eq_top with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    rwa [← hkereq]
  · exfalso
    have hsup : ψ.ker ⊔ Subgroup.center S = ⊤ := by
      have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center S))) h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h1
    set π := QuotientGroup.mk' ψ.ker with hπ
    have hmap : (Subgroup.center S).map π = ⊤ := by
      have h1 := congrArg (Subgroup.map π) hsup
      rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
        (Subgroup.map_eq_bot_iff _).mpr (by rw [hπ, QuotientGroup.ker_mk']), bot_sup_eq] at h1
    have hcommle : _root_.commutator ↥S ≤ ψ.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      have ha : π a ∈ Subgroup.center (↥S ⧸ ψ.ker) :=
        Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
          (hmap ▸ Subgroup.mem_top (π a))
      rw [← QuotientGroup.ker_mk' ψ.ker, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp ha (π b)).symm
    have htop : ψ.ker = ⊤ := by
      rw [eq_top_iff, ← hperf.commutator_eq_top]
      exact hcommle
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥(J i))
    obtain ⟨x, rfl⟩ := hsurj y
    exact hy (by rw [← MonoidHom.mem_ker, htop]; exact Subgroup.mem_top x)

theorem nonempty_quotient_ker_subgroupOf_equiv {Y : Type*} [Group Y] (f : X →* Y)
    (S : Subgroup X) : Nonempty (S ⧸ f.ker.subgroupOf S ≃* S.map f) := by
  have hker : (f.domRestrict S).ker = f.ker.subgroupOf S := MonoidHom.ker_restrict S f
  have hrange : (f.domRestrict S).range = S.map f := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange (f.domRestrict S)).trans
      (MulEquiv.subgroupCongr hrange))⟩

end CFSG.LieType.BorelTits.RadicalLinear
