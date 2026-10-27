module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Comp
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_le_sSup_sup_glaPComponent {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (S : Set (Subgroup G)) (hS : ∀ L ∈ S, GLAPComponent p X L) (hK : GLAPComponent p X K)
    (h : K ≤ sSup S ⊔ GLAPPrimeCoreOf p X) : K ∈ S := by
  by_contra hKS
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  set E : Subgroup G := ((Subgroup.centralizer
    (barX p X K : Set (↥X ⧸ GLAPPrimeCore p ↥X))).comap π).map X.subtype with hE
  have hLE : ∀ L ∈ S, L ≤ E := by
    intro L hL l hl
    have hne : L ≠ K := fun h' => hKS (h' ▸ hL)
    have hl' : l ∈ X := (hS L hL).1 hl
    refine ⟨⟨l, hl'⟩, ?_, rfl⟩
    have hcent := barX_le_centralizer (p := p) (C := X) (S := L) (T := K)
      (fun s hs t ht _ _ => by
        have := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp
          (hS L hL) hK hne (Subgroup.commutator_mem_commutator hs ht)
        simpa [commutatorElement_def] using this)
    exact hcent ⟨⟨l, hl'⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  have hOE : GLAPPrimeCoreOf p X ≤ E := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, ?_, rfl⟩
    show π o ∈ Subgroup.centralizer _
    rw [show π o = 1 from (QuotientGroup.eq_one_iff o).2 ho]
    exact Subgroup.one_mem _
  have hKE : K ≤ E := h.trans (sup_le (sSup_le hLE) hOE)
  have hq : CFSG.Open.IsQuasisimple ↥(barX p X K) := hK.2.2.1.2.2
  have hcomm : ∀ a b : ↥(barX p X K), a * b = b * a := by
    rintro ⟨_, k1, hk1, rfl⟩ ⟨_, k2, hk2, rfl⟩
    have hk1' : (k1 : G) ∈ K := Subgroup.mem_subgroupOf.1 hk1
    obtain ⟨k1', hk1'', hk1e⟩ := hKE hk1'
    have hk1e' : k1' = k1 := Subtype.ext hk1e
    subst hk1e'
    have := Subgroup.mem_centralizer_iff.1 hk1'' (π k2) ⟨k2, hk2, rfl⟩
    exact Subtype.ext this.symm
  have hbot : commutator ↥(barX p X K) ≤ ⊥ := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b)
  rw [hq.1] at hbot
  have hsub : Subsingleton ↥(barX p X K) :=
    ⟨fun a b => by
      have ha : a ∈ (⊥ : Subgroup ↥(barX p X K)) := hbot (Subgroup.mem_top a)
      have hb : b ∈ (⊥ : Subgroup ↥(barX p X K)) := hbot (Subgroup.mem_top b)
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]⟩
  have := hq.2.toNontrivial
  have : Subsingleton (↥(barX p X K) ⧸ Subgroup.center ↥(barX p X K)) :=
    (QuotientGroup.mk'_surjective _).subsingleton
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) this

theorem le_centModSubgroup_of_ne {p : ℕ} (hp : p.Prime) {X K L : Subgroup G}
    (hK : GLAPComponent p X K) (hL : GLAPComponent p X L) (hne : K ≠ L) :
    K ≤ centModSubgroup p L := by
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp hL hK hne.symm hk
  refine ⟨hkN, fun l hl => ?_⟩
  have h1 : ⁅l, k⁆ ∈ GLAPPrimeCoreOf p X := by
    have := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp hL hK
      hne.symm
    exact this (Subgroup.commutator_mem_commutator hl hk)
  have h2 : ⁅l, k⁆ ∈ L := by
    have : k * l⁻¹ * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hkN l⁻¹).1 (L.inv_mem hl)
    have e : ⁅l, k⁆ = l * (k * l⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem hl this
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
  exact ⟨h2, h1⟩

theorem closureIn_le_centModSubgroup {p : ℕ} (hp : p.Prime) {B K L : Subgroup G} {x : G}
    (hBCx : B ≤ Subgroup.centralizer ({x} : Set G))
    (hK : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) K)
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hBK : ¬ B ≤ Subgroup.normalizer (K : Set G)) :
    closureIn K B ≤ centModSubgroup p L := by
  refine iSup₂_le fun b hb => ?_
  have hKb : K.map (MulAut.conj b).toMonoidHom = GLBConj b⁻¹ K := by
    unfold GLBConj
    rw [inv_inv]
  rw [hKb]
  have hbCx : b⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.inv_mem _ (hBCx hb))
  have hKbc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) (GLBConj b⁻¹ K) := by
    have := glaPComponent_gLBConj hK b⁻¹
    rwa [mem_normalizer_iff_gLBConj_eq.1 hbCx] at this
  refine le_centModSubgroup_of_ne hp hKbc hL fun heq => hBK ?_
  have hKL : K = L := by
    have h1 : GLBConj b (GLBConj b⁻¹ K) = K := by
      rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one]
    rw [← h1, heq, mem_normalizer_iff_gLBConj_eq.1 (hBL hb)]
  rw [hKL]
  exact hBL

theorem mem_of_le_sSup_glaPComponent {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (S : Set (Subgroup G)) (hS : ∀ L ∈ S, GLAPComponent p X L) (hK : GLAPComponent p X K)
    (h : K ≤ sSup S) : K ∈ S :=
  mem_of_le_sSup_sup_glaPComponent hp S hS hK (h.trans le_sup_left)

end CFSG.LocalAnalysis.GLTheoremA
