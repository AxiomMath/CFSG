module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Lift
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem simple_nonabelian_of_lieModel {Y : Type} [Group Y] {p f : ℕ}
    (h : Blueprint.LieModel Y .PSL 2 p f) : IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨-, -, h2, h3, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data h
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hF]; exact h2))
      (Or.inr (by rw [hF]; exact h3))
  obtain ⟨x, y, hxy⟩ := CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F
    (by rw [hF]; exact h2) (by rw [hF]; exact h3)
  exact ⟨e.isSimpleGroup, e.symm x, e.symm y, fun hc => hxy (by simpa using congrArg e hc)⟩

end L415

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

structure Config415 (hs : Setting46e t L p f S w z V i j)
    (Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (W : Subgroup X)
    (z₁ : X) : Prop where
  prod : L415.IsProd (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) Kb₁ Kb₂
    (hs.setup.tBar i j)
  KBar_eq : Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j}
  equiv₁ : Nonempty (↥Kb₁ ≃* ↥(Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  isSylowOf_W : IsSylowOf 2 W (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
  U_le : V ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ≤ W
  z₁_mem : z₁ ∈ W
  sq_z₁ : z₁ ^ 2 = 1
  z_eq : z = z₁ * (t * z₁ * t⁻¹)
  z₁_ne : z₁ ≠ t * z₁ * t⁻¹
  mk_z₁ : ∀ hz₁ : z₁ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
    (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ Kb₁
  comm_iff : ∀ x ∈ W, ∀ hx : x ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
    x * z₁ = z₁ * x ↔ Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).toMonoidHom = Kb₁
  mul_t : ∀ x ∈ W, x * z₁ ≠ z₁ * x → x * t * z₁ = z₁ * (x * t)
  card_le : 8 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ≤ Nat.card W

theorem Setting46e.exists_config415 (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hnq : ¬ IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    ∃ (Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (W : Subgroup X)
      (z₁ : X), Config415 hs Kb₁ Kb₂ W z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  have h45 := hs.lemma45
  rcases h412.lemma46d with ⟨hq, -⟩ | ⟨Kb₁, Kb₂, hsup, hinf, hcen, hmap, ⟨e₁⟩, -, hlie, hK, -⟩
  · exact absurd hq hnq
  obtain ⟨hsimp, hnab⟩ := L415.simple_nonabelian_of_lieModel hlie
  have hprod : L415.IsProd (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) Kb₁ Kb₂
      (hs.setup.tBar i j) :=
    { sup_eq := hsup
      inf_eq := hinf
      le_centralizer := hcen
      map_conj := hmap
      simple := e₁.isSimpleGroup
      nonabelian := by
        obtain ⟨a, b, hab⟩ := hnab
        exact ⟨e₁.symm a, e₁.symm b, fun hc => hab (by simpa using congrArg e₁ hc)⟩ }
  obtain ⟨W, hW, hUW⟩ := hs.exists_W
  have htM := hσ.t_mem_centralizer_beta i j
  have ht2 : t * t = 1 := by
    rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hTU := hs.beta.lt.le
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hTU.trans hUW
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  set Dst := S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hDst
  have hDT : Dst ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
    inf_le_left.trans (le_sup_right.trans le_sup_left)
  have hDW : Dst ≤ W := hDT.trans hTW
  have hKM := Standing.Setup42.K_le_centralizer_beta (L := L) (t := t) (w := w) (z := z) i j
  have hDsyl : IsSylowOf 2 (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) Dst)
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {QuotientGroup.mk ⟨t, htM⟩}) := by
    have h1 : IsSylowOf 2 (Dst.subgroupOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}))
        ((centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subgroupOf
          (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) := by
      rw [← isSylowOf_map_subtype_iff, subgroupOf_map_subtype, subgroupOf_map_subtype,
        inf_of_le_left (inf_le_right.trans hKM), inf_of_le_left hKM]
      exact h45.isSylowOf_Dstar
    have h2 := HarrisLit.isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
      ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) h1
    have h3 : Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {QuotientGroup.mk ⟨t, htM⟩} := hK
    rw [← h3]
    exact h2
  obtain ⟨m, hm, ⟨eD⟩⟩ := h45.dihedral_Dstar
  have hzD : z ∈ Dst := h45.z_mem
  have hzc : ∀ d ∈ Dst, z * d = d * z := by
    intro d hd
    have hz : z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
      rw [hσ.center_D]
      exact mem_zpowers z
    exact ((mem_centralizer_iff.mp hz.2) d hd.1).symm
  have hz1 : z ≠ 1 := fun h1 => by
    have := hσ.z_order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  obtain ⟨z₁, hz₁W, hz₁2, hzz, hz₁ne, hmk, hcomm, hmul, hcard⟩ :=
    L415.exists_z₁ htM ht2 hprod hW htW hDW hDsyl hm eD hzD hzc hz1
  refine ⟨Kb₁, Kb₂, W, z₁, ⟨hprod, hK, ⟨e₁⟩, hW, hUW, hz₁W, hz₁2, hzz, hz₁ne, hmk, hcomm,
    hmul, ?_⟩⟩
  have h1 := hcard _ hTW (hσ.T_le.trans hs.sylow.le)
  have h2 : 8 ≤ Nat.card Dst := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
    calc 8 = 2 * 2 ^ 2 := by norm_num
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hm)
  calc 8 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
      ≤ Nat.card Dst * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :=
        Nat.mul_le_mul_right _ h2
    _ ≤ Nat.card W := h1

end CFSG.ComponentClassification.HarrisLit
