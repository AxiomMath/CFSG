module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Goldschmidt75.TheoremBcN1
import CFSG.LocalAnalysis.GLTheoremA.Lemma48
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MLayer
import CFSG.Milestones.ASVolI.I2Covers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def centralModTwo (L : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ L ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L}
  mul_mem' := by
    rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
    refine ⟨L.mul_mem hxL hyL, fun l hl => ?_⟩
    have h1 := CFSG.ASVolI.burnsideI22P5_pCoreOf_conj_of_normal L L
      (fun c hc n hn => L.mul_mem (L.mul_mem hc hn) (L.inv_mem hc)) x hxL _ (hy l hl)
    have : x * y * l * (x * y)⁻¹ * l⁻¹ =
        (x * (y * l * y⁻¹ * l⁻¹) * x⁻¹) * (x * l * x⁻¹ * l⁻¹) := by group
    rw [this]
    exact (pCoreOf 2 L).mul_mem h1 (hx l hl)
  one_mem' := ⟨L.one_mem, fun l _ => by simp [(pCoreOf 2 L).one_mem]⟩
  inv_mem' := by
    rintro x ⟨hxL, hx⟩
    refine ⟨L.inv_mem hxL, fun l hl => ?_⟩
    have hl' : x⁻¹ * l * x ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hxL) hl) hxL
    have h := (pCoreOf 2 L).inv_mem (hx _ hl')
    have : x⁻¹ * l * x⁻¹⁻¹ * l⁻¹ = (x * (x⁻¹ * l * x) * x⁻¹ * (x⁻¹ * l * x)⁻¹)⁻¹ := by group
    rw [this]
    exact h

theorem conj_mem_centralModTwo {L : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hx : x ∈ centralModTwo L) :
    g * x * g⁻¹ ∈ centralModTwo L := by
  obtain ⟨hxL, hx⟩ := hx
  have hgL : ∀ h : G, h ∈ L ↔ g * h * g⁻¹ ∈ L := fun h => Subgroup.mem_normalizer_iff.mp hg h
  refine ⟨(hgL x).mp hxL, fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ L := by
    rw [hgL]
    simpa [mul_assoc] using hl
  have h := CFSG.ASVolI.burnsideI22P5_pCoreOf_conj L g hgL (hx _ hl')
  have : g * x * g⁻¹ * l * (g * x * g⁻¹)⁻¹ * l⁻¹ =
      g * (x * (g⁻¹ * l * g) * x⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ := by group
  rw [this]
  exact h

theorem mem_zpowers_of_cyclic_center {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hcyc : IsCyclic ↥(Subgroup.center ↥B)) {b c : G} (hbB : b ∈ B)
    (hb : ∀ x ∈ B, b * x = x * b) (hbo : orderOf b = p) (hcB : c ∈ B)
    (hc : ∀ x ∈ B, c * x = x * c) (hco : orderOf c = p) : b ∈ Subgroup.zpowers c := by
  set S : Subgroup G := ((Subgroup.center ↥B).map B.subtype) with hS
  have hSc : IsCyclic ↥S :=
    isCyclic_of_surjective ((Subgroup.center ↥B).equivMapOfInjective B.subtype
      B.subtype_injective).toMonoidHom (MulEquiv.surjective _)
  have hmem : ∀ {x : G} (hxB : x ∈ B), (∀ y ∈ B, x * y = y * x) → x ∈ S := by
    intro x hxB hx
    refine ⟨⟨x, hxB⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    exact Subtype.ext (hx y y.2).symm
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.zpowers_eq_of_orderOf_eq_of_isCyclic hSc
    (hmem hbB hb) (hmem hcB hc) (hbo.trans hco.symm)
  rw [← h]
  exact Subgroup.mem_zpowers b

theorem mem_of_cyclic_center {p : ℕ} [Fact p.Prime] {B N : Subgroup G} (hBp : IsPGroup p B)
    (hcyc : IsCyclic ↥(Subgroup.center ↥B)) {b : G} (hbB : b ∈ B)
    (hb : ∀ x ∈ B, b * x = x * b) (hbo : orderOf b = p) (hNB : N ≤ B)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) : b ∈ N := by
  have hne := CFSG.Goldschmidt75.inf_centralizer_ne_bot hBp hNB hBN hN
  set D := N ⊓ Subgroup.centralizer (B : Set G) with hD
  have hDp : IsPGroup p D := hBp.to_le (inf_le_left.trans hNB)
  haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn⟩ := hDp.nontrivial_iff_card.mp inferInstance
  obtain ⟨c, hco⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) p (by
    rw [hn.2]
    exact dvd_pow_self p hn.1.ne')
  have hcN : (c : G) ∈ N := c.2.1
  have hcC : (c : G) ∈ Subgroup.centralizer (B : Set G) := c.2.2
  have hco' : orderOf (c : G) = p := by rw [Subgroup.orderOf_coe]; exact hco
  have hbc := mem_zpowers_of_cyclic_center hcyc hbB hb hbo (hNB hcN)
    (fun x hx => (Subgroup.mem_centralizer_iff.mp hcC x hx).symm) hco'
  exact (Subgroup.zpowers_le.mpr hcN) hbc

theorem eq_of_cyclic_center {p : ℕ} [Fact p.Prime] {B T : Subgroup G} {b : G}
    (hBC : CFSG.ABGLocalTools.IsSylowOf p B (Subgroup.centralizer ({b} : Set G)))
    (hcyc : IsCyclic ↥(Subgroup.center ↥B)) (hbB : b ∈ B) (hbo : orderOf b = p)
    (hT : IsPGroup p T) (hBT : B ≤ T) : T = B := by
  have hp : p.Prime := Fact.out
  have hBc : B ≤ Subgroup.centralizer ({b} : Set G) := hBC.le
  have hb : ∀ x ∈ B, b * x = x * b := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hBc hx)).symm
  have hNT : T ⊓ Subgroup.normalizer (B : Set G) = B := by
    refine le_antisymm ?_ (le_inf hBT (Subgroup.le_normalizer))
    have hcard : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hbo]
    have hle : T ⊓ Subgroup.normalizer (B : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
      rintro x ⟨-, hxN⟩
      have hxb : x * b * x⁻¹ ∈ Subgroup.zpowers b := by
        have hxB : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hxN b).mp hbB
        refine mem_zpowers_of_cyclic_center hcyc hxB (fun y hy => ?_) ?_ hbB hb hbo
        · have hy' : x⁻¹ * y * x ∈ B := by
            have := (Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * y * x)).mpr
            exact this (by simpa [mul_assoc] using hy)
          have := hb _ hy'
          calc x * b * x⁻¹ * y = x * (b * (x⁻¹ * y * x)) * x⁻¹ := by group
            _ = x * ((x⁻¹ * y * x) * b) * x⁻¹ := by rw [this]
            _ = y * (x * b * x⁻¹) := by group
        · have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective b
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
          rw [this, hbo]
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        rw [← conj_zpow]
        exact Subgroup.zpow_mem _ hxb k
      · intro hh
        have hcomm : x * b * x⁻¹ ∈ Subgroup.zpowers b := hxb
        have hsub : (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom ≤
            Subgroup.zpowers b := by
          rw [Subgroup.map_le_iff_le_comap]
          intro u hu
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
          change x * b ^ k * x⁻¹ ∈ Subgroup.zpowers b
          rw [← conj_zpow]
          exact Subgroup.zpow_mem _ hxb k
        have heq : (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b :=
          Subgroup.eq_of_le_of_card_ge hsub (by
            rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
        rw [← heq] at hh
        obtain ⟨u, hu, hux⟩ := hh
        have : u = h := by
          have : x * u * x⁻¹ = x * h * x⁻¹ := hux
          simpa using this
        rwa [← this]
    have hcent := CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq hp
      (hT.to_le inf_le_left) hcard hle
    have hC : T ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hcent hx) b (Subgroup.mem_zpowers b)).symm
    rw [hBC.eq_of_le (le_inf hBT Subgroup.le_normalizer) hC (hT.to_le inf_le_left)]
  exact (CFSG.LocalAnalysis.GLTheoremB.MovingAround.eq_of_normalizer_inf_eq hT hBT hNT).symm

theorem commutator_le_of_cyclic_center {p : ℕ} [Fact p.Prime] {M L B : Subgroup G} {b c : G}
    (hBC : CFSG.ABGLocalTools.IsSylowOf p B (Subgroup.centralizer ({b} : Set G)))
    (hBM : B ≤ M) (hcyc : IsCyclic ↥(Subgroup.center ↥B)) (hbB : b ∈ B) (hbo : orderOf b = p)
    (hLM : L ≤ M) (hML : M ≤ Subgroup.normalizer (L : Set G)) (hpL : p ∣ Nat.card L)
    (hc1 : c ≠ 1) (hcB : c ∈ B) (hcL : b ∈ L → c ∈ L)
    (hcT : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ⁅Subgroup.zpowers b, L⁆ ≤ pCoreOf 2 L := by
  have hBp : IsPGroup p B := hBC.isPGroup
  have hb : ∀ x ∈ B, b * x = x * b := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hBC.le hx)).symm
  have hBsylM : CFSG.ABGLocalTools.IsSylowOf p B M := by
    obtain ⟨Q, hQ⟩ := (hBp.comap_subtype (K := M)).exists_le_sylow
    have hQp : IsPGroup p ((Q : Subgroup M).map M.subtype) := Q.isPGroup'.map _
    have hBQ : B ≤ (Q : Subgroup M).map M.subtype := fun x hx => ⟨⟨x, hBM hx⟩, hQ hx, rfl⟩
    have := eq_of_cyclic_center hBC hcyc hbB hbo hQp hBQ
    exact ⟨Q, this⟩
  have hBL := hBsylM.inf_of_le_normalizer hLM hML
  have hBLne : B ⊓ L ≠ ⊥ := by
    obtain ⟨Q, hQ⟩ := hBL
    rw [← hQ]
    intro h
    have hQb : (Q : Subgroup L) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (x : G) ∈ (Q : Subgroup L).map L.subtype := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
    exact Q.ne_bot_of_dvd_card hpL hQb
  have hBnorm : ∀ {N : Subgroup G}, B ≤ Subgroup.normalizer (N : Set G) →
      B ≤ Subgroup.normalizer ((B ⊓ N : Subgroup G) : Set G) := by
    intro N hN x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun ⟨h1, h2⟩ => ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) h).mp h1,
        (Subgroup.mem_normalizer_iff.mp (hN hx) h).mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) h).mpr h1,
        (Subgroup.mem_normalizer_iff.mp (hN hx) h).mpr h2⟩⟩
  have hbL : b ∈ L :=
    (mem_of_cyclic_center hBp hcyc hbB hb hbo inf_le_left (hBnorm (hBM.trans hML)) hBLne).2
  have hcT₀ : c ∈ centralModTwo L := ⟨hcL hbL, hcT⟩
  have hBT : B ≤ Subgroup.normalizer ((centralModTwo L : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => conj_mem_centralModTwo (hML (hBM hx)) hh, fun hh => ?_⟩
    have := conj_mem_centralModTwo (g := x⁻¹) (hML (hBM (B.inv_mem hx))) hh
    simpa [mul_assoc] using this
  have hne : B ⊓ centralModTwo L ≠ ⊥ := by
    intro h
    have : c ∈ B ⊓ centralModTwo L := ⟨hcB, hcT₀⟩
    rw [h] at this
    exact hc1 (Subgroup.mem_bot.mp this)
  have hbT := (mem_of_cyclic_center hBp hcyc hbB hb hbo inf_le_left (hBnorm hBT) hne).2
  rw [Subgroup.commutator_le]
  intro g hg l hl
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((centralModTwo L).zpow_mem hbT k).2 l hl

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
