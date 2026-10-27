module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212Layer
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

structure Lemma212Component (p : ℕ) {X : Type*} [Group X] (z : X) (D : Subgroup X)
    (L : Subgroup X) : Prop where
  isComponent : IsComponentOf L ⊤
  normal : L.Normal
  unique : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = L
  mem : z ∈ L
  central : ∀ g ∈ L, g * z = z * g
  center_ne_bot : center L ≠ ⊥
  isPGroup_center : IsPGroup p (center L)
  omega : ∀ c ∈ L, (∀ g ∈ L, g * c = c * g) → c ^ p = 1 → c ∈ zpowers z
  pElement : ∀ x ∈ L ⊓ centralizer (D : Set X), (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ D

section Component

variable {X : Type} [Group X] [Finite X] {n p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}
  {L : Subgroup X}

namespace Lemma212Component

theorem exists_not_commute [Fact p.Prime] (hL : Lemma212Component p z D L)
    (h : Lemma212ConfigGe n p P z D) (hcore : primeComplementCore (G := X) p = ⊥) {d : X}
    (hd : d ∈ D) (hdz : d ∉ zpowers z) : ∃ y ∈ L, d * y ≠ y * d := by
  have hp : p.Prime := Fact.out
  by_contra hno
  push Not at hno
  have hDc : ∀ v ∈ D, ∀ y ∈ L, v * y = y * v := by
    intro v hv y hy
    obtain ⟨s, t, rfl⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hd hdz hv
    have h1 : Commute d y := hno y hy
    have h2 : Commute z y := (hL.central y hy).symm
    exact ((h1.pow_left s).mul_left (h2.pow_left t)).eq
  obtain ⟨-, x, hxL, ⟨k, hxk⟩, g0, hg0L, hg0x⟩ :=
    exists_pElement_not_central hp hcore hL.isComponent
  have hxD : x ∈ D :=
    hL.pElement x ⟨hxL, mem_centralizer_iff.2 fun v hv => hDc v hv x hxL⟩ ⟨k, hxk⟩
  exact hg0x (hDc x hxD g0 hg0L).symm

theorem le_of_conj_eq [Fact p.Prime] (hL : Lemma212Component p z D L)
    (h : Lemma212ConfigGe n p P z D) (hcore : primeComplementCore (G := X) p = ⊥) {d : X}
    (hd : d ∈ D) (hdz : d ∉ zpowers z) {l : X} (hlL : l ∈ L)
    (hconj : ∀ y ∈ L, l * y * l⁻¹ = d * y * d⁻¹) : D ≤ L := by
  have hp : p.Prime := Fact.out
  obtain ⟨y0, hy0L, hy0⟩ := hL.exists_not_commute h hcore hd hdz
  obtain ⟨c, hc⟩ : ∃ c : X, d = l * c := ⟨l⁻¹ * d, by simp⟩
  have hcL : ∀ y ∈ L, c * y = y * c := by
    intro y hy
    have h1 := hconj y hy
    rw [hc] at h1
    have h2 : c * y * c⁻¹ = y := by
      calc c * y * c⁻¹ = l⁻¹ * (l * c * y * (l * c)⁻¹) * l := by group
        _ = l⁻¹ * (l * y * l⁻¹) * l := by rw [h1]
        _ = y := by group
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hlc : Commute l c := (hcL l hlL).symm
  have hdp : d ^ p = 1 := h.elem.2 d hd
  have hlcp : l ^ p * c ^ p = 1 := by rw [← hlc.mul_pow, ← hc]; exact hdp
  have hlpc : l ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hlcp
  have hcpl : c ^ p = (l ^ p)⁻¹ := by rw [hlpc, inv_inv]
  have hcg : ∀ g ∈ L, Commute (l ^ p) g := by
    intro g hg
    rw [hlpc]
    exact ((show Commute c g from hcL g hg).pow_left p).inv_left
  have hctr : (⟨l ^ p, pow_mem hlL p⟩ : L) ∈ center L :=
    mem_center_iff.2 fun g => Subtype.ext (hcg g g.2).symm.eq
  obtain ⟨k, hk⟩ := hL.isPGroup_center ⟨⟨l ^ p, pow_mem hlL p⟩, hctr⟩
  have hk' : (l ^ p) ^ p ^ k = 1 := by
    simpa using congrArg (fun w : ↥(center L) => (((w : L) : X))) hk
  have hck : c ^ p ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul, hcpl, inv_pow, hk', inv_one]
  have hcD : c ∈ centralizer (D : Set X) := by
    refine mem_centralizer_iff.2 fun v hv => ?_
    obtain ⟨s, t, rfl⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hd hdz hv
    have h1 : Commute d c := by rw [hc]; exact hlc.mul_left (Commute.refl c)
    have h2 : Commute z c := (hcL z hL.mem).symm
    exact ((h1.pow_left s).mul_left (h2.pow_left t)).eq
  have hcD' : c ∈ D := h.mem_of_pElement_mem_centralizer hp hcD ⟨k + 1, hck⟩
  have hcz : c ∈ zpowers z := by
    by_contra hcz
    obtain ⟨s, t, hdst⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hcD' hcz hd
    apply hy0
    rw [hdst]
    have h1 : Commute c y0 := hcL y0 hy0L
    have h2 : Commute z y0 := (hL.central y0 hy0L).symm
    exact ((h1.pow_left s).mul_left (h2.pow_left t)).eq
  have hcL' : c ∈ L := zpowers_le.2 hL.mem hcz
  have hdL : d ∈ L := by rw [hc]; exact mul_mem hlL hcL'
  intro v hv
  obtain ⟨s, t, rfl⟩ :=
    exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hd hdz hv
  exact mul_mem (pow_mem hdL s) (pow_mem hL.mem t)

theorem false_of_le [Fact p.Prime] (hL : Lemma212Component p z D L)
    (h : Lemma212ConfigGe n p P z D) (h5 : 5 ≤ p) (hDL : D ≤ L)
    (hbar : IsLinearOrUnitaryAt p (L ⧸ center L)) (hR : GL83PElementCentralizerRank) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨d, hd, hdz⟩ := h.exists_mem_notMem_zpowers hp
  have hdL : d ∈ L := hDL hd
  have hd'p : (⟨d, hdL⟩ : L) ^ p = 1 := Subtype.ext (h.elem.2 d hd)
  have hd'c : (⟨d, hdL⟩ : L) ∉ center L := by
    intro hmem
    apply hdz
    exact hL.omega d hdL (fun g hg => congrArg Subtype.val (mem_center_iff.1 hmem ⟨g, hg⟩))
      (h.elem.2 d hd)
  have hrank := hR p hp h5 L hL.isComponent.2.2 hbar hL.center_ne_bot hL.isPGroup_center
    ⟨d, hdL⟩ hd'p hd'c
  have h1 := CFSG.SectionRank.pRank_le_map hp.one_lt L.subtype L.subtype_injective
    (centralizer ({(⟨d, hdL⟩ : L)} : Set L))
  have hle : (centralizer ({(⟨d, hdL⟩ : L)} : Set L)).map L.subtype ≤ centralizer (D : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro v hv
    obtain ⟨s, t, rfl⟩ :=
      exists_pow_mul_pow_of_mem_plane h.elem h.card h.mem (h.ne_one hp) hd hdz hv
    have h2 : Commute d (y : X) := (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)).symm
    have h3 : Commute z (y : X) := (hL.central y y.2).symm
    exact ((h2.pow_left s).mul_left (h3.pow_left t)).eq
  have h2 := CFSG.SectionRank.pRank_mono hp.one_lt hle
  have h3 := pRank_le_of_isSylowOf hp h.sylow h.card
  omega

theorem false_of_not_le [Fact p.Prime] (hL : Lemma212Component p z D L)
    (h : Lemma212ConfigGe n p P z D) (h5 : 5 ≤ p) (hcore : primeComplementCore (G := X) p = ⊥)
    {g : X} (hg : IsPlaneDiagonal p D z g) (hbar : IsLinearOrUnitaryAt p (L ⧸ center L))
    (hB : GL83OutDiagPowerMap) (hDL : ¬ D ≤ L) : False := by
  have hp : p.Prime := Fact.out
  haveI := hL.normal
  obtain ⟨d, hd, hdz⟩ := h.exists_mem_notMem_zpowers hp
  obtain ⟨a, b, hab, -, hsq, hne, hga, hgd⟩ := hg.exists_sq_ne_one h5
  obtain ⟨c, hc⟩ := hgd d hd hdz
  have hδp : (MulAut.conjNormal d : MulAut L) ^ p = 1 := by
    rw [← map_pow, h.elem.2 d hd, map_one]
  have hδinn : (MulAut.conjNormal d : MulAut L) ∉ (MulAut.conj : L →* MulAut L).range := by
    rintro ⟨l, hl⟩
    refine hDL (hL.le_of_conj_eq h hcore hd hdz l.2 fun y hy => ?_)
    have := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : X)) hl
    simpa [MulAut.conjNormal_apply] using this
  have hz : (MulAut.conjNormal z : MulAut L) = 1 := by
    ext y
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.2 (hL.central y y.2).symm
  have hαδ : (MulAut.conjNormal g : MulAut L) * MulAut.conjNormal d *
      (MulAut.conjNormal g)⁻¹ = (MulAut.conjNormal d) ^ b := by
    rw [← map_inv, ← map_mul, ← map_mul, hc, map_mul, map_pow, map_pow, hz, one_pow, mul_one]
  have hαc : ∀ c' ∈ center L, c' ^ p = 1 → (MulAut.conjNormal g : MulAut L) c' = c' ^ a := by
    intro c' hc'ctr hc'p
    have hmem : (c' : X) ∈ zpowers z :=
      hL.omega c' c'.2 (fun g' hg' => congrArg Subtype.val (mem_center_iff.1 hc'ctr ⟨g', hg'⟩))
        (by simpa using congrArg Subtype.val hc'p)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, Subgroup.coe_pow, ← hk, ← conj_zpow, hga, ← zpow_natCast,
      ← zpow_mul, ← zpow_natCast (z ^ k) a, ← zpow_mul, mul_comm]
  have hone : (a : ZMod p) * b = 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hab
    rwa [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
  rcases hB p hp h5 L hL.isComponent.2.2 hbar hL.center_ne_bot hL.isPGroup_center _ _ a b hδp
    hδinn hαδ hαc with hab' | hb1
  · exact hne hab'
  · rw [hb1, mul_one] at hone
    exact hsq (by rw [hone]; norm_num)

end Lemma212Component

end Component

end CFSG.LocalAnalysis.RankFourTheoremC
