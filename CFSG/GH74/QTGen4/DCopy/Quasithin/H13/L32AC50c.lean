module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32AC50c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC49a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2
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

local notation "cS7" =>
  (MulAut.conjNormal : Equiv.Perm (Fin 7) →* MulAut CFSG.Quasithin.H13.L32A.C.Alt7.A7)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem exists_pi_a7_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h28 : Lemma14_7_28_F4)
    (h32 : Lemma14_7_32_F4) (h47 : Lemma14_7_47_F4) (h48 : Lemma14_7_48_F4) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hA : IsAlt 7 (cStar K)) :
    ∃ π : ↥H →* Equiv.Perm (Fin 7), π.ker = CFSG.Open.pCore 2 ↥H ∧
      alternatingGroup (Fin 7) ≤ π.range := by
  obtain ⟨K', hcK', -, -⟩ := h48 _ T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hL1K := (h47 _ T L V H S K hK).1
  have hKn := le_normalizer_of_setting h37 h38 S hK (h32 _ T L V H S K hK)
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨φ⟩ := hA
  set π₀ : ↥K →* ↥(alternatingGroup (Fin 7)) := φ.toMonoidHom.comp (QuotientGroup.mk' _)
    with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := indHom π₀ hπ₀ hker₀ hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π₀ k) = π₀ (conjK (hKn y.2) k) :=
    indHom_apply π₀ hπ₀ hker₀ hKn hHN
  have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = cS7 (π₀ ⟨k, hk⟩ : Equiv.Perm (Fin 7)) := by
    intro k hk
    have e : MulAut.conj (π₀ ⟨k, hk⟩) = cS7 (π₀ ⟨k, hk⟩ : Equiv.Perm (Fin 7)) := by
      ext x
      simp [MulAut.conjNormal_apply]
    rw [← e]
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ₀ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hInn : ∀ y : ↥H, β y ∈ MonoidHom.range cS7 := fun y => Alt7.conjNormal_surjective _
  have hZ : Subgroup.center (cStar K) = ⊥ := by
    have hc := card_center_eq_of_mulEquiv φ
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc
  obtain ⟨ψ, hψ, hψker⟩ := quotIso_of_range π₀ hπ₀ hker₀ hKH hKn hHN cS7
    Alt7.conjNormal_injective hInn fun x hx hxc => mem_pCoreOf_of_comm_F4 h28 S hcK' hL1K hKn hZ hx hxc
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = (π₀ ⟨k, hk⟩ : Equiv.Perm (Fin 7)) := by
    intro k hk
    apply Alt7.conjNormal_injective
    rw [hψ, hKin k hk]
  refine ⟨ψ, hψker, fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := hπ₀ ⟨a, ha⟩
  exact ⟨⟨k, hKH k.2⟩, (hψK k k.2).trans (congrArg Subtype.val hk)⟩

end CFSG.Quasithin.H13.L32A.C
