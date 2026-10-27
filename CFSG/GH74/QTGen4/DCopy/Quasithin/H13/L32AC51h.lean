module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32AC51h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC49a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A5Props
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A767a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A767b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A769c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AStatements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Equiv Equiv.Perm

local notation "cS8" =>
  (MulAut.conjNormal : Equiv.Perm (Fin 8) →* MulAut CFSG.Quasithin.H13.L32A.C.Alt8)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem false_of_graph_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h4 : Lemma14_7_4_two_three_F4) (h28 : Lemma14_7_28_F4) (hMod : Lemma14_7_51_Mod_F4)
    (S : Setting147 G T L V H) {K : Subgroup G} (hcK : cComp H = {K}) (hHKT : H = K ⊔ T)
    (hL1K : l1 T L V ≤ K) (hP : IsPSL 4 2 1 (cStar K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {π : ↥K →* Lin.SLn 4}
    (hπ : Function.Surjective π) (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    {t₀ : G} (ht₀ : t₀ ∈ H)
    (hout : indHom π hπ hker hKn hHN ⟨t₀, ht₀⟩ ∉
      (MulAut.conj : Lin.SLn 4 →* MulAut (Lin.SLn 4)).range) : False := by
  have hK : K ∈ cComp H := by rw [hcK]; exact Set.mem_singleton K
  have hKH : K ≤ H := le_of_mem_cComp hK
  set ι := Lin.slFourEquivAlt8 with hι
  set π' : ↥K →* Alt8 := ι.toMonoidHom.comp π with hπ'def
  have hπ' : Function.Surjective π' := ι.surjective.comp hπ
  have hker' : ∀ k : ↥K, π' k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker]
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN
  set β' := indHom π' hπ' hker' hKn hHN with hβ'def
  have hβ' : ∀ (y : ↥H) (k : ↥K), β' y (π' k) = π' (conjK (hKn y.2) k) :=
    indHom_apply π' hπ' hker' hKn hHN
  have hKin : ∀ k (hk : k ∈ K), β' ⟨k, hKH hk⟩ = cS8 (π' ⟨k, hk⟩ : Perm (Fin 8)) := by
    intro k hk
    have e : MulAut.conj (π' ⟨k, hk⟩) = cS8 (π' ⟨k, hk⟩ : Perm (Fin 8)) := by
      ext x
      simp [MulAut.conjNormal_apply]
    rw [← e]
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ' a
    rw [hβ', MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hZ : Subgroup.center (cStar K) = ⊥ := by
    obtain ⟨φ⟩ := Lin.nonempty_mulEquiv_sl_of_isPSL hP
    have hc := card_center_eq_of_mulEquiv φ
    rw [Lin.center_eq_bot, Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc
  obtain ⟨ψ, hψ, hψker⟩ := quotIso_of_range π' hπ' hker' hKH hKn hHN cS8
    Lin.conjNormal_injective8 (fun y => Lin.conjNormal_surjective8 _)
    fun x hx hxc => mem_pCoreOf_of_comm_F4 h28 S hcK hL1K hKn hZ hx hxc
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = (π' ⟨k, hk⟩ : Perm (Fin 8)) := by
    intro k hk
    apply Lin.conjNormal_injective8
    rw [hψ, hKin k hk]

  have hA8 : alternatingGroup (Fin 8) ≤ ψ.range := by
    intro a ha
    obtain ⟨k, hk⟩ := hπ' ⟨a, ha⟩
    exact ⟨⟨k, hKH k.2⟩, by rw [hψK k k.2, hk]⟩
  have hnot : ψ ⟨t₀, ht₀⟩ ∉ alternatingGroup (Fin 8) := by
    intro ha
    set b : Alt8 := ⟨ψ ⟨t₀, ht₀⟩, ha⟩ with hb
    have hcb : β' ⟨t₀, ht₀⟩ = MulAut.conj b := by
      rw [← hψ]
      ext x
      simp [MulAut.conjNormal_apply, hb]
    apply hout
    refine ⟨ι.symm b, ?_⟩
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := hπ x
    apply ι.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hβ]
    have h1 := hβ' ⟨t₀, ht₀⟩ k
    rw [hcb, MulAut.conj_apply] at h1
    exact h1
  have hψs : Function.Surjective ψ := MonoidHom.range_eq_top.mp
    (Lin.eq_top_of_alt8 hA8 ⟨⟨t₀, ht₀⟩, rfl⟩ hnot)

  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod' := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp h13322 hMod' h1222
  have h2 := hMod G T L V H S K hK hHKT hL1K hP ψ hψs hψker V₂ hV2
  have h1 := (h4 _ T L V V₂ S.hyp hV2).2.2.2.2
  omega

end CFSG.Quasithin.H13.L32A.C
