module

public import CFSG.CGT.PushingUpLit.BHS6.SymAltFacts
public import CFSG.CGT.PushingUpLit.BHS6.SymAssembly
public import CFSG.CGT.PushingUpLit.BHS6.SymAssemblyBlock

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] {n : ℕ} {G T V : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)}
  {ψ : ↥V →* ↥(coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

structure SymJoin (G T V : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) (ψ : ↥V →* ↥(coreMod n))
    (E : Subgroup Γ) : Prop where
  le : E ≤ G
  residual : oResidualTwo ↥E = ⊤
  commutator : ⁅E, baum T⁆ = E
  img_eq_alt : imgG G φ E = alternatingGroup (Fin n)
  nonCentral : ⁅E, omegaOneCenterOf T⁆ ≠ ⊥
  ker_psi : ∃ k : ↥V, (k : Γ) ∈ E ⊓ Subgroup.centralizer (V : Set Γ) ∧ ψ k ≠ 1

variable {E : Subgroup Γ}

namespace SymJoin

theorem map_mem_alt (h : SymJoin G T V φ ψ E) {e : Γ} (he : e ∈ E) :
    φ ⟨e, h.le he⟩ ∈ alternatingGroup (Fin n) :=
  map_mem_alternating_of_oResidualTwo h.residual h.le he

theorem le_normalizer_ker (h : SymJoin G T V φ ψ E) (hVn : G ≤ Subgroup.normalizer (V : Set Γ)) :
    E ≤ Subgroup.normalizer
      ((E ⊓ Subgroup.centralizer (V : Set Γ) : Subgroup Γ) : Set Γ) :=
  fun _ he => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer he, B6.le_normalizer_centralizer hVn (h.le he)⟩

theorem ker_le_pCore (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E)
    (hKV : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ V) :
    E ⊓ Subgroup.centralizer (V : Set Γ) ≤ pCoreOf 2 (E) := by
  have hVpc : V ≤ pCoreOf 2 G := S.vQ.trans (C1GN.omegaOneCenterOf_le_self _)
  have hK2 : IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (V : Set Γ)) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G).to_le (hKV.trans hVpc)
  exact le_pCoreOf_of_normalizes inf_le_left (le_normalizer_ker h S.data.normal) hK2

theorem pCore_le_ker (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E) (h5 : 5 ≤ n) :
    pCoreOf 2 (E) ≤ E ⊓ Subgroup.centralizer (V : Set Γ) := by
  classical
  have hEG : E ≤ G := h.le
  let α : ↥E →* alternatingGroup (Fin n) := altRestrict φ hEG fun _ he => h.map_mem_alt he
  have hαs : Function.Surjective α := by
    intro σ
    have hσ : (σ : Equiv.Perm (Fin n)) ∈ imgG G φ E := by
      rw [h.img_eq_alt]
      exact σ.2
    obtain ⟨e, heG, heE, hφe⟩ := mem_imgG.1 hσ
    exact ⟨⟨e, heE⟩, Subtype.ext hφe⟩
  have hOEE : pCoreOf 2 E ≤ E := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E
  have hQnormal : ((pCoreOf 2 E).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOEE).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E)
  have hQp : IsPGroup 2 ↥((pCoreOf 2 E).subgroupOf E) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E).of_equiv
      (Subgroup.subgroupOfEquivOfLe hOEE).symm
  have hbot : ((pCoreOf 2 E).subgroupOf E).map α = ⊥ :=
    eq_bot_of_normal_isPGroup_alternating h5 (hQnormal.map _ hαs) (hQp.map _)
  intro p hp
  have hpE : p ∈ E := hOEE hp
  have h1 : α ⟨p, hpE⟩ = 1 := by
    have : α ⟨p, hpE⟩ ∈ ((pCoreOf 2 E).subgroupOf E).map α :=
      ⟨⟨p, hpE⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have h2 : φ ⟨p, hEG hpE⟩ = 1 := congrArg Subtype.val h1
  have h3 : (⟨p, hEG hpE⟩ : ↥G) ∈ φ.ker := h2
  rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h3
  exact ⟨hpE, h3.2⟩

theorem pCoreOf_eq (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E)
    (h5 : 5 ≤ n) (hKV : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ V) :
    pCoreOf 2 (E) = E ⊓ Subgroup.centralizer (V : Set Γ) :=
  le_antisymm (pCore_le_ker S h h5) (ker_le_pCore S h hKV)

theorem psi_surj_ker (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E) (h5 : 5 ≤ n)
    (y : ↥(coreMod n)) :
    ∃ k : ↥V, (k : Γ) ∈ E ⊓ Subgroup.centralizer (V : Set Γ) ∧ ψ k = y := by
  classical
  set K : Subgroup Γ := E ⊓ Subgroup.centralizer (V : Set Γ) with hK
  have hnorm := le_normalizer_ker h S.data.normal
  let X : Subgroup ↥(coreMod n) := (K.subgroupOf V).map ψ
  have hX : ∀ σ ∈ alternatingGroup (Fin n), ∀ x ∈ X, coreAct n σ x ∈ X := by
    intro σ hσ x hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hσ' : σ ∈ imgG G φ E := by
      rw [h.img_eq_alt]
      exact hσ
    obtain ⟨e, heG, heE, hφe⟩ := mem_imgG.1 hσ'
    have hkK : (k : Γ) ∈ K := hk
    have hv : e * (k : Γ) * e⁻¹ ∈ V := S.data.conj_mem heG k.2
    have h1 := S.data.equivar ⟨e, heG⟩ k hv
    refine ⟨⟨e * (k : Γ) * e⁻¹, hv⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hnorm heE) k).mp hkK
    · rw [h1, hφe]
  have hne : X ≠ ⊥ := by
    obtain ⟨k, hkK, hk1⟩ := h.ker_psi
    intro hbot
    apply hk1
    have : ψ k ∈ X := ⟨k, hkK, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have htop := eq_top_of_invariant_ne_bot S.odd (by omega) X hX hne
  have hy : y ∈ X := by
    rw [htop]
    trivial
  obtain ⟨k, hk, hky⟩ := hy
  exact ⟨k, hk, hky⟩

theorem map_eq_one_of_mem_centralizer_ker (S : SymSetting G T V n φ ψ T')
    (h : SymJoin G T V φ ψ E) (h5 : 5 ≤ n) {e : Γ} (he : e ∈ E)
    (hec : e ∈ Subgroup.centralizer ((E ⊓ Subgroup.centralizer (V : Set Γ) : Subgroup Γ) :
      Set Γ)) : φ ⟨e, h.le he⟩ = 1 := by
  apply coreAct_injective (by omega : 3 ≤ n)
  rw [map_one]
  refine MulEquiv.ext fun y => ?_
  obtain ⟨k, hk, rfl⟩ := psi_surj_ker S h h5 y
  have hv : e * (k : Γ) * e⁻¹ ∈ V := S.data.conj_mem (h.le he) k.2
  have h1 := S.data.equivar ⟨e, h.le he⟩ k hv
  have hck : (k : Γ) * e = e * (k : Γ) := Subgroup.mem_centralizer_iff.mp hec k hk
  have h2 : (⟨e * (k : Γ) * e⁻¹, hv⟩ : ↥V) = k := by
    apply Subtype.ext
    show e * (k : Γ) * e⁻¹ = k
    rw [← hck]
    group
  rw [h2] at h1
  rw [MulAut.one_apply]
  exact h1.symm

theorem altRestrict_surjective (h : SymJoin G T V φ ψ E) :
    Function.Surjective (altRestrict φ h.le fun _ he => h.map_mem_alt he) := by
  intro σ
  have hσ : (σ : Equiv.Perm (Fin n)) ∈ imgG G φ (E) := by
    rw [h.img_eq_alt]
    exact σ.2
  obtain ⟨e, heG, heE, hφe⟩ := mem_imgG.1 hσ
  exact ⟨⟨e, heE⟩, Subtype.ext hφe⟩

theorem charTwo (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E) (h5 : 5 ≤ n)
    (hKV : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ V) : CharTwo (E) := by
  intro e he
  obtain ⟨heE, hec⟩ := he
  rw [pCoreOf_eq S h h5 hKV] at hec ⊢
  have h1 := map_eq_one_of_mem_centralizer_ker S h h5 heE hec
  have h2 : (⟨e, h.le heE⟩ : ↥G) ∈ φ.ker := h1
  rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
  exact ⟨heE, h2.2⟩

theorem isNatAlt (S : SymSetting G T V n φ ψ T') (h : SymJoin G T V φ ψ E) (h5 : 5 ≤ n)
    (hKV : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ V) :
    IsNatAlt (E) (pCoreOf 2 (E)) n := by
  classical
  have hPK : pCoreOf 2 E = E ⊓ Subgroup.centralizer (V : Set Γ) := pCoreOf_eq S h h5 hKV
  have hPV : pCoreOf 2 E ≤ V := hPK.le.trans hKV
  have hEG : E ≤ G := h.le
  have h3 : 3 ≤ n := by omega
  refine ⟨altRestrict φ hEG fun _ he => h.map_mem_alt he, ψ.comp (Subgroup.inclusion hPV),
    altRestrict_surjective h, ?_, ?_, ?_, ?_⟩
  · ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      have h2 : φ ⟨e, hEG e.2⟩ = 1 := congrArg Subtype.val h1
      have h3' : (⟨e, hEG e.2⟩ : ↥G) ∈ φ.ker := h2
      rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h3'
      exact ⟨e.2, Subgroup.centralizer_le hPV h3'.2⟩
    · rintro ⟨-, hec⟩
      rw [hPK] at hec
      exact Subtype.ext (map_eq_one_of_mem_centralizer_ker S h h5 e.2 hec)
  · intro y
    obtain ⟨k, hk, hky⟩ := psi_surj_ker S h h5 y
    exact ⟨⟨k, hPK ▸ hk⟩, hky⟩
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      have h2 : (⟨(w : Γ), hPV w.2⟩ : ↥V) ∈ ψ.ker := h1
      rw [S.data.ψ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
      exact ⟨w.2, Subgroup.centralizer_le hEG h2.2⟩
    · rintro ⟨-, hwc⟩
      show ψ ⟨(w : Γ), hPV w.2⟩ = 1
      refine eq_one_of_fixed_alt S.odd h3 _ fun σ hσ => ?_
      have hσ' : σ ∈ imgG G φ E := by
        rw [h.img_eq_alt]
        exact hσ
      obtain ⟨e, heG, heE, hφe⟩ := mem_imgG.1 hσ'
      have hv : e * (w : Γ) * e⁻¹ ∈ V := S.data.conj_mem heG (hPV w.2)
      have h1 := S.data.equivar ⟨e, heG⟩ ⟨w, hPV w.2⟩ hv
      have hew : e * (w : Γ) = (w : Γ) * e := Subgroup.mem_centralizer_iff.mp hwc e heE
      have h2 : (⟨e * (w : Γ) * e⁻¹, hv⟩ : ↥V) = ⟨w, hPV w.2⟩ := by
        apply Subtype.ext
        show e * (w : Γ) * e⁻¹ = w
        rw [hew]
        group
      rw [h2, hφe] at h1
      exact h1.symm
  · intro e w hw
    exact S.data.equivar ⟨e, hEG e.2⟩ ⟨w, hPV w.2⟩ (hPV hw)

theorem isBTBlock {m : ℕ} (hm : 2 ≤ m) {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))}
    {ψ : ↥V →* ↥(coreMod (2 * m + 1))} {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}
    (S : SymSetting G T V (2 * m + 1) φ ψ T') (h : SymJoin G T V φ ψ E)
    (hKV : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ V)
    (hKE : ⁅(E ⊓ Subgroup.centralizer (V : Set Γ) : Subgroup Γ), E⁆ =
      E ⊓ Subgroup.centralizer (V : Set Γ)) : IsBTBlock G T (E) := by
  have h5 : 5 ≤ 2 * m + 1 := by omega
  have hPK := pCoreOf_eq S h h5 hKV
  have hPV : pCoreOf 2 (E) ≤ V := hPK.le.trans hKV
  have hperf : ⁅pCoreOf 2 (E), E⁆ = pCoreOf 2 (E) := by
    rw [hPK]
    exact hKE
  have hab : ∀ x ∈ pCoreOf 2 (E), ∀ y ∈ pCoreOf 2 (E), x * y = y * x := by
    intro x hx y hy
    have h1 := S.data.elemAbelian.1.is_comm.comm (⟨x, hPV hx⟩ : ↥V) ⟨y, hPV hy⟩
    exact congrArg Subtype.val h1
  exact ⟨h.le, h.residual, h.commutator, hperf, ⟨hab, fun x hx => S.data.elemAbelian.2 x (hPV hx)⟩,
    h.nonCentral, Or.inr ⟨m, by omega, isNaturalAltModule_of_isNatAlt (charTwo S h h5 hKV) hab
      hperf (isNatAlt S h h5 hKV)⟩⟩


end SymJoin

end CFSG.CGT.PushingUpLit.SYMB
