module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Layer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Setup
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt46E

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.L64

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem Em_le_Em_of_Em_le {G : Type} [Group G] {N H : Subgroup G} (hEH : Em N ≤ H) (hHN : H ≤ N) :
    Em N ≤ Em H := by
  rw [Em_def, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  have hKH : K.map N.subtype ≤ H := (Subgroup.map_mono (le_sSup hK)).trans hEH
  have hKle : K ≤ H.subgroupOf N := fun k hk => hKH ⟨k, hk, rfl⟩
  have hcomp : IsComponent (K.subgroupOf (H.subgroupOf N)) :=
    CFSG.LocalCores.component_overgroup hK hKle
  let f : ↥(H.subgroupOf N) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHN
  have hcomp2 : IsComponent ((K.subgroupOf (H.subgroupOf N)).map f.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv f hcomp
  have hle : (K.subgroupOf (H.subgroupOf N)).map f.toMonoidHom ≤ layer ↥H := le_sSup hcomp2
  intro k hk
  rw [Subgroup.mem_comap]
  exact ⟨f ⟨k, hKle hk⟩, hle ⟨⟨k, hKle hk⟩, hk, rfl⟩, rfl⟩

theorem lemma6_4_of (h63 : Lemma6_3) (h46 : Lemma4_6E) : Lemma6_4 := by
  intro G _ _ z k S M p hC N A B r hH
  have hF : Fm N ≤ M := h63 G z k S M p hC N A B r hH
  have hFs : Fs N = Fm N ⊔ Em N := by
    rw [Fs_def, Fm_def, Em_def, ← Subgroup.map_sup]
    rfl
  suffices hE : Em N ≤ M by
    rw [hFs]
    exact sup_le hF hE
  by_contra hEM
  have hzN : z ∈ N := hH.z_mem
  have hzM : z ∈ M := hC.z_mem
  have hPN : P1 z M N r ≤ N := P1_le_N hzN
  have hHN : Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z ≤ N :=
    sup_le (sup_le (sup_le (Em_le N) hPN) E1_le_N) (Subgroup.zpowers_le.mpr hzN)
  have hHne : Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z ≠ ⊤ := fun h =>
    hH.maximal.1 (top_le_iff.mp (h ▸ hHN))
  have hEmH : Em N ≤ Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z :=
    le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hPH : P1 z M N r ≤ Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hEH : E1 M N r ≤ Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z :=
    le_sup_right.trans le_sup_left
  have hzH : z ∈ Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hsig : Sig4Sub G z (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z) r (P1 z M N r) := by
    have s : Sig4Sub G z N r (P1 z M N r) := sig4Sub hC hH
    exact ⟨hHne, s.A.prime, s.A.odd, hzH, hPH, s.A.pgroup, s.A.ne_bot,
      fun c hc hcz => s.A.inv c (hHN hc) hcz, s.A.comm⟩
  have hEmle : Em N ≤ Em (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z) :=
    Em_le_Em_of_Em_le hEmH hHN
  have hne : ⁅Em (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z), P1 z M N r⁆ ≠ ⊥ := by
    intro hbot
    apply hEM
    have hcen : Em (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z) ≤
        centralizer ((P1 z M N r : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact (hEmle.trans hcen).trans (centralizer_P1_le hH)
  have hEcen : E1 M N r ≤ (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z) ⊓
      centralizer ((P1 z M N r : Subgroup G) : Set G) :=
    le_inf hEH (E1_le_centralizer_P1 hC hH)
  have hEnorm : ((E1 M N r).subgroupOf ((Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z) ⊓
      centralizer ((P1 z M N r : Subgroup G) : Set G))).Normal :=
    normal_E1_of_le hC hH hEH hHN
  have hzE : z ∈ normalizer ((E1 M N r : Subgroup G) : Set G) := mem_normalizer_E1 hzM hzN
  have hEodd : Odd (Nat.card ↥(E1 M N r)) := odd_card_E1 hC
  have hEr : ¬ r ∣ Nat.card ↥(E1 M N r) := fun hd =>
    hH.prime.ne_one (Nat.Coprime.eq_one_of_dvd (coprime_card_E1 hH) hd)
  have hcent : E1 M N r ≤ centralizer
      ((⁅Em (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z), P1 z M N r⁆ : Subgroup G) : Set G) :=
    h46 G z k S hC.ctx _ _ r hsig hne _ hEcen hEnorm hzE hEodd hEr
  have hKM : ⁅Em (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z), P1 z M N r⁆ ≤ M := by
    have hB : B ≤ centralizer
        ((⁅Em (Em N ⊔ P1 z M N r ⊔ E1 M N r ⊔ zpowers z), P1 z M N r⁆ : Subgroup G) : Set G) :=
      (B_le_E1 hH).trans hcent
    exact (Subgroup.le_centralizer_iff.mp hB).trans
      ((Subgroup.centralizer_le_normalizer _).trans hH.B_mem.2.2.2)
  have hNM : ⁅Em N, P1 z M N r⁆ ≤ M := (Subgroup.commutator_mono hEmle le_rfl).trans hKM
  apply hEM
  refine (Em_le_comm_sup_centralizer hPN).trans (sup_le hNM ?_)
  exact inf_le_right.trans (centralizer_P1_le hH)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.L64
