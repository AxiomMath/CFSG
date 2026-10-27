module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Std

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action

structure StdCfg {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) where
  hcs : ConstrainedSetting G T M H S L
  hj : conjJoin S L = L
  F : H247Facts T H S L
  D : ModData H L
  hsurj : Function.Surjective D.π
  hker : ∀ h : ↥H, D.π h = 1 ↔ (h : G) ∈ pCoreOf 2 H
  hRE : ∀ (r : G) (hr : r ∈ baum S), D.π ⟨r, baum_le_H hcs hr⟩ ∈ Estd
  hRE' : ∀ σ ∈ Estd, ∃ (r : G) (hr : r ∈ baum S), D.π ⟨r, baum_le_H hcs hr⟩ = σ
  hHeq : H = L ⊔ baum S

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem blockU_le_H (C : StdCfg T M H S L) : blockU L ≤ H :=
  (blockU_le_S C.hcs C.hj).trans C.hcs.sylow.le

theorem pCoreOf_le_S (C : StdCfg T M H S L) : pCoreOf 2 H ≤ S := C56.pCoreOf_le_S C.hcs

theorem sylow_card_perm_five (P : Sylow 2 (Equiv.Perm (Fin 5))) : Nat.card P = 8 := by
  rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)),
    Fintype.card_perm]
  have h120 : (Nat.factorial (Fintype.card (Fin 5))) = 2 ^ 3 * 15 := by
    rw [Fintype.card_fin]; decide
  rw [h120, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h15]

theorem card_piS (C : StdCfg T M H S L) : Nat.card ((S.subgroupOf H).map C.D.π) = 8 := by
  have hS := C.hcs.sylow
  have hS' : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 H := hS'.toSylow hS.2.2
  have h1 := sylow_card_perm_five (P.mapSurjective C.hsurj)
  have h2 : ((P.mapSurjective C.hsurj : Sylow 2 (Equiv.Perm (Fin 5))) :
      Subgroup (Equiv.Perm (Fin 5))) = (S.subgroupOf H).map C.D.π := by
    rw [Sylow.coe_mapSurjective]
    rfl
  rw [← h2]
  exact h1

theorem piS_eq (C : StdCfg T M H S L) : (S.subgroupOf H).map C.D.π = Dstd := by
  set PS := (S.subgroupOf H).map C.D.π with hPS
  have hE : Estd ≤ PS := by
    intro σ hσ
    obtain ⟨r, hr, hπ⟩ := C.hRE' σ hσ
    exact ⟨⟨r, baum_le_H C.hcs hr⟩, Subgroup.mem_subgroupOf.mpr (baum_le_S hr), hπ⟩
  have hcard : Nat.card PS = 8 := C.card_piS
  have h1 := C5.card_eq_card_mul_relIndex hE
  rw [hcard, Estd_card] at h1
  have hidx : (Estd.subgroupOf PS).index = 2 := by
    have : Estd.relIndex PS = 2 := by omega
    exact this
  have hn : (Estd.subgroupOf PS).Normal := Subgroup.normal_of_index_eq_two hidx
  have hnorm : PS ≤ Subgroup.normalizer (Estd : Set (Equiv.Perm (Fin 5))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE).mp hn
  have hle : PS ≤ Dstd := by
    intro σ hσ
    rw [mem_Dstd, mem_Dset]
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp (hnorm hσ) x).mp hx
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Dstd_card, hcard])

theorem pi_mem_Dstd (C : StdCfg T M H S L) {s : G} (hs : s ∈ S) :
    C.D.π ⟨s, C.hcs.sylow.le hs⟩ ∈ Dstd := by
  rw [← C.piS_eq]
  exact ⟨⟨s, C.hcs.sylow.le hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩

theorem exists_mem_S_pi (C : StdCfg T M H S L) {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ Dstd) :
    ∃ (s : G) (hs : s ∈ S), C.D.π ⟨s, C.hcs.sylow.le hs⟩ = σ := by
  rw [← C.piS_eq] at hσ
  obtain ⟨y, hy, rfl⟩ := hσ
  exact ⟨y.1, Subgroup.mem_subgroupOf.mp hy, rfl⟩

theorem exists_Khat (C : StdCfg T M H S L) :
    ∃ K : Subgroup G, K ≤ H ∧ ∀ k : ↥H, (k : G) ∈ K ↔ C.D.π k ∈ S4std := by
  refine ⟨(S4std.comap C.D.π).map H.subtype, by rintro _ ⟨k, -, rfl⟩; exact k.2, fun k => ?_⟩
  constructor
  · rintro ⟨k', hk', hkk⟩
    have : k' = k := Subtype.ext hkk
    subst this
    exact hk'
  · intro hk
    exact ⟨k, hk, rfl⟩

theorem pi_MH (C : StdCfg T M H S L) (h : ↥H) (hM : (h : G) ∈ M) : C.D.π h ∈ S4std := by
  by_contra hne
  rw [mem_S4std] at hne
  obtain ⟨Khat, hKH, hKmem⟩ := C.exists_Khat
  have hKhatM : Khat ≤ M := by
    apply C.hcs.maxInf Khat
    · intro s hs
      have := (hKmem ⟨s, C.hcs.sylow.le hs⟩).mpr (by
        rw [mem_S4std]
        exact Dset_le_S4 _ ((mem_Dstd _).mp (C.pi_mem_Dstd hs)))
      exact this
    · refine lt_of_le_of_ne hKH ?_
      intro heq
      obtain ⟨k, hk⟩ := C.hsurj (Equiv.swap 0 4)
      have hkK : (k : G) ∈ Khat := heq ▸ k.2
      have := (hKmem k).mp hkK
      rw [hk, mem_S4std] at this
      simp at this
  let Y : Subgroup (Equiv.Perm (Fin 5)) := ((M ⊓ H).subgroupOf H).map C.D.π
  have hY : S4std ≤ Y := by
    intro σ hσ
    obtain ⟨k, hk⟩ := C.hsurj σ
    refine ⟨k, ?_, hk⟩
    refine Subgroup.mem_subgroupOf.mpr ⟨hKhatM ((hKmem k).mpr ?_), k.2⟩
    rw [hk]; exact hσ
  have hπh : C.D.π h ∈ Y := ⟨h, Subgroup.mem_subgroupOf.mpr ⟨hM, h.2⟩, rfl⟩
  have hYtop : Y = ⊤ := S4_max Y hY _ hπh hne
  apply C.hcs.not_le
  intro l hl
  have hlH : l ∈ H := C56.le_H C.hcs hl
  have hmem : C.D.π ⟨l, hlH⟩ ∈ Y := hYtop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hπy⟩ := hmem
  have hker : (⟨l, hlH⟩ * y⁻¹ : ↥H) ∈ C.D.π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπy, mul_inv_cancel]
  have hQ' : ((⟨l, hlH⟩ * y⁻¹ : ↥H) : G) ∈ pCoreOf 2 H := (C.hker _).mp hker
  have hSM : S ≤ M := C.hcs.sylow_inf.le.trans inf_le_right
  have hlM : l * (y : G)⁻¹ ∈ M := hSM (C.pCoreOf_le_S hQ')
  have hyM : (y : G) ∈ M := (Subgroup.mem_subgroupOf.mp hy).1
  have : l = (l * (y : G)⁻¹) * y := by group
  rw [this]
  exact mul_mem hlM hyM

theorem z0_mem : z0 ∈ evenWeight 5 := by
  rw [mem_evenWeight_iff]; decide +kernel

@[expose] def z0V : evenWeight 5 := ⟨z0, z0_mem⟩

@[expose] noncomputable def zUsub (C : StdCfg T M H S L) : ↥(blockU L) :=
  C.D.β.symm (Multiplicative.ofAdd z0V)

@[expose] noncomputable def zU (C : StdCfg T M H S L) : G := (C.zUsub : G)

theorem zU_mem (C : StdCfg T M H S L) : C.zU ∈ blockU L := (C.zUsub).2

theorem beta_zUsub (C : StdCfg T M H S L) : Multiplicative.toAdd (C.D.β C.zUsub) = z0V := by
  simp [zUsub]

theorem zU_ne_one (C : StdCfg T M H S L) : C.zU ≠ 1 := by
  intro h
  have h1 : C.zUsub = 1 := Subtype.ext h
  have h2 := C.beta_zUsub
  rw [h1, map_one] at h2
  have := congrArg Subtype.val h2
  revert this
  show ¬ ((0 : evenWeight 5) : Fin 5 → ZMod 2) = z0
  decide +kernel

theorem zU_sq (C : StdCfg T M H S L) : C.zU ^ 2 = 1 :=
  C1.blockU_sq (C56.isShort C.hcs) _ C.zU_mem

theorem conj_zU_iff (C : StdCfg T M H S L) (h : ↥H) :
    (h : G) * C.zU * (h : G)⁻¹ = C.zU ↔ pact (C.D.π h) z0 = z0 := by
  have hmem := H_normalizes_U C.hcs C.hj h h.2 C.zU C.zU_mem
  have key := C.D.hβ h C.zUsub ⟨_, hmem⟩ rfl
  rw [C.beta_zUsub] at key
  constructor
  · intro h1
    have : (⟨_, hmem⟩ : ↥(blockU L)) = C.zUsub := Subtype.ext h1
    rw [this, C.beta_zUsub] at key
    exact congrArg Subtype.val key.symm
  · intro h1
    have h2 : vact (C.D.π h) z0V = z0V := Subtype.ext h1
    rw [h2] at key
    have := C.D.β.injective (Multiplicative.toAdd.injective (key.trans (C.beta_zUsub).symm))
    exact congrArg Subtype.val this

theorem zU_central_S (C : StdCfg T M H S L) {s : G} (hs : s ∈ S) :
    s * C.zU * s⁻¹ = C.zU := by
  have := (C.conj_zU_iff ⟨s, C.hcs.sylow.le hs⟩).mpr
    (z0_fixed _ (Dset_le_S4 _ ((mem_Dstd _).mp (C.pi_mem_Dstd hs))))
  exact this

theorem CU_S (C : StdCfg T M H S L) {u : G} (hu : u ∈ blockU L)
    (hc : ∀ s ∈ S, s * u * s⁻¹ = u) : u = 1 ∨ u = C.zU := by
  set w := Multiplicative.toAdd (C.D.β ⟨u, hu⟩) with hw
  have hfix : ∀ σ ∈ Dset, pact σ w.1 = w.1 := by
    intro σ hσ
    obtain ⟨s, hs, hπ⟩ := C.exists_mem_S_pi ((mem_Dstd σ).mpr hσ)
    have hmem := H_normalizes_U C.hcs C.hj s (C.hcs.sylow.le hs) u hu
    have key := C.D.hβ ⟨s, C.hcs.sylow.le hs⟩ ⟨u, hu⟩ ⟨_, hmem⟩ rfl
    have h1 : (⟨s * u * s⁻¹, hmem⟩ : ↥(blockU L)) = ⟨u, hu⟩ := Subtype.ext (hc s hs)
    rw [h1, hπ] at key
    exact (congrArg Subtype.val key).symm
  rcases fixed_Dset w.1 w.2 hfix with h | h
  · left
    have h' : w = 0 := Subtype.ext h
    have : C.D.β ⟨u, hu⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h'
      simpa [hw] using this
    have h2 := C.D.β.injective (this.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  · right
    have h' : w = z0V := Subtype.ext h
    have : C.D.β ⟨u, hu⟩ = C.D.β C.zUsub := by
      apply Multiplicative.toAdd.injective
      rw [C.beta_zUsub]
      exact h'
    exact congrArg Subtype.val (C.D.β.injective this)

end StdCfg

end CFSG.QuasithinUnique.A5
