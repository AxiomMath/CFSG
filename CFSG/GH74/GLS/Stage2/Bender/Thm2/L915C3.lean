module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915D1

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement Pointwise

@[expose] def NoL3Overgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, Cen z ≤ H → H ≠ ⊤ → ∀ J : Subgroup G, J ≤ H → IsQuasisimple ↥J → z ∈ J →
      (∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) →
      ∀ p n : ℕ, p.Prime → p ≠ 2 → 1 ≤ n → LieModel (↥J ⧸ center ↥J) .PSL 3 p n → False

namespace L915

section OpFacts

variable {G : Type} [Group G]

theorem le_Op_of_normalized {p : ℕ} {L X : Subgroup G} (hXL : X ≤ L)
    (hn : L ≤ normalizer (X : Set G)) (hX : IsPGroup p ↥X) : X ≤ Op p L := by
  have hnorm : (X.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr hn
  have hpg : IsPGroup p ↥(X.subgroupOf L) :=
    hX.of_injective (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXL).injective
  have h1 : X.subgroupOf L ≤ pCore p ↥L := le_sSup ⟨hnorm, hpg⟩
  have h2 : (X.subgroupOf L).map L.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXL
  rw [Op_eq_map, ← h2]
  exact Subgroup.map_mono h1

theorem normalizer_Op_of_normal {p : ℕ} {L N : Subgroup G}
    (hn : N ≤ normalizer (L : Set G)) : N ≤ normalizer ((Op p L : Subgroup G) : Set G) := by
  have key : ∀ y ∈ N, ∀ o ∈ Op p L, y * o * y⁻¹ ∈ Op p L := by
    intro y hy o ho
    set X : Subgroup G := (Op p L).map (MulAut.conj y).toMonoidHom with hX
    have hLy : ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun l hl => (mem_normalizer_iff.mp (hn hy) l).mp hl
    have hLy' : ∀ l ∈ L, y⁻¹ * l * y ∈ L := fun l hl => by
      have := (mem_normalizer_iff.mp (hn (N.inv_mem hy)) l).mp hl
      simpa using this
    have hXL : X ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hLy x (Op_le' p L hx)
    have hnX : L ≤ normalizer (X : Set G) := by
      intro l hl
      rw [mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨(y⁻¹ * l * y) * x * (y⁻¹ * l * y)⁻¹, ?_, ?_⟩
        · exact (mem_normalizer_iff.mp (le_normalizer_Op' p L (hLy' l hl)) x).mp hx
        · show y * ((y⁻¹ * l * y) * x * (y⁻¹ * l * y)⁻¹) * y⁻¹ = l * (y * x * y⁻¹) * l⁻¹
          group
      · rintro ⟨x, hx, hxg⟩
        refine ⟨(y⁻¹ * l⁻¹ * y) * x * (y⁻¹ * l⁻¹ * y)⁻¹, ?_, ?_⟩
        · have : y⁻¹ * l⁻¹ * y ∈ L := hLy' _ (L.inv_mem hl)
          exact (mem_normalizer_iff.mp (le_normalizer_Op' p L this) x).mp hx
        · show y * ((y⁻¹ * l⁻¹ * y) * x * (y⁻¹ * l⁻¹ * y)⁻¹) * y⁻¹ = g
          have hxg' : y * x * y⁻¹ = l * g * l⁻¹ := hxg
          calc y * ((y⁻¹ * l⁻¹ * y) * x * (y⁻¹ * l⁻¹ * y)⁻¹) * y⁻¹
              = l⁻¹ * (y * x * y⁻¹) * l := by group
            _ = g := by rw [hxg']; group
    have hXp : IsPGroup p ↥X := (op_isPGroup L).map (MulAut.conj y).toMonoidHom
    exact le_Op_of_normalized hXL hnX hXp ⟨o, ho, rfl⟩
  intro y hy
  rw [mem_normalizer_iff]
  intro o
  exact ⟨fun ho => key y hy o ho, fun ho => by
    have := key y⁻¹ (N.inv_mem hy) _ ho
    simpa [mul_assoc] using this⟩

end OpFacts

section A0

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {N A B : Subgroup G}

theorem noc_of_component {J : Subgroup ↥N} (hJ : IsComponent J) (hO2' : pCore 2 ↥N = ⊥) :
    ∀ c ∈ J.map N.subtype, (∀ g ∈ J.map N.subtype, c * g = g * c) → c * c = 1 → c = 1 := by
  rintro _ ⟨c, hc, rfl⟩ hcomm hc2
  have hcc : c ∈ centralizer (J : Set ↥N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subtype.ext (hcomm (g : G) ⟨g, hg, rfl⟩).symm
  have : c = 1 := eq_one_of_central_involution hO2' hJ hc hcc (Subtype.ext hc2)
  rw [this]
  rfl

theorem a0_eq_bot (hK1 : K1Statement) (hNo : NoL3Overgroup) (hC : Ctx9 G z k S M p)
    (h : Hyp95 z M p N A B) (hO2 : Op 2 N = ⊥) (hAE : ¬ A ≤ centralizer (Em N : Set G))
    (hcC : C43c (zSec z N (z_mem_N h) (pCore p ↥N)) p (xBar p N (A1 z M N p))) :
    Op p M ⊓ N ⊓ Cen z = ⊥ := by
  by_contra hA₀
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hzN : z ∈ N := z_mem_N h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨J, n, hn, hJ, hJn, hOJ, -, hzJ, -, hLie, -, -, -⟩ := exists_caseC_J hC h hAE hcC
  have hO2' : pCore 2 ↥N = ⊥ := by
    have := hO2
    rw [Op_eq_map, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hC.orderOf_z, pow_two] at h1
    exact h1
  have hz1 : z ≠ 1 := by
    intro h1
    have := hC.orderOf_z
    rw [h1, orderOf_one] at this
    omega
  set z' : ↥N := ⟨z, hzN⟩ with hz'
  have hz2' : z' * z' = 1 := Subtype.ext hz2
  have hz1' : z' ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  set A₀ : Subgroup G := Op p M ⊓ N ⊓ Cen z with hA₀def
  have hA₀N : A₀ ≤ N := inf_le_left.trans inf_le_right
  have hA₀P : A₀ ≤ Op p M := inf_le_left.trans inf_le_left
  have hA₀p : IsPGroup p ↥A₀ := hC.P_pgroup.to_le hA₀P
  have hA₀'p : IsPGroup p ↥(A₀.subgroupOf N) :=
    hA₀p.of_injective (Subgroup.subgroupOfEquivOfLe hA₀N).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hA₀N).injective
  have hnormA₀ : ∀ c : G, c * z = z * c → c ∈ N → c ∈ normalizer (A₀ : Set G) := by
    intro c hcz hcN
    have hcC : c ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hcz
    have hcM : c ∈ M := hC.cen_le hcC
    exact Thm1.mem_normalizer_inf (Thm1.mem_normalizer_inf (le_normalizer_Op' p M hcM)
      (Subgroup.le_normalizer hcN))
      (mem_normalizer_centralizer_of_comm (S := {z}) fun s hs => by
        rw [Set.mem_singleton_iff.mp hs]; exact hcz.symm)
  have hA₀'n : ∀ c : ↥N, c * z' = z' * c → c ∈ normalizer ((A₀.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    intro c hc
    have h1 := hnormA₀ (c : G) (congrArg Subtype.val hc) c.2
    rw [mem_normalizer_iff]
    intro x
    have h2 := (mem_normalizer_iff.mp h1) (x : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using h2
  have hA₀'z : ∀ a ∈ A₀.subgroupOf N, a * z' = z' * a := by
    intro a ha
    have : (a : G) ∈ Cen z := (Subgroup.mem_subgroupOf.mp ha).2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp this)
  have hcent : A₀.subgroupOf N ≤ centralizer (J : Set ↥N) :=
    centralizes_of_K1 hK1 hp hp2 hn hO2' hJ hJn hLie hzJ hz2' hz1' hA₀'p hA₀'z hA₀'n
  set L : Subgroup G := (centralizer (J : Set ↥N)).map N.subtype with hL
  have hLN : L ≤ N := Subgroup.map_subtype_le _
  have hLz : L ≤ Cen z := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp hy z' hzJ
    exact (congrArg Subtype.val this).symm
  have hLnorm : N ≤ normalizer (L : Set G) := by
    have key : ∀ n ∈ N, ∀ g ∈ L, n * g * n⁻¹ ∈ L := by
      rintro n hn _ ⟨y, hy, rfl⟩
      refine ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, ?_, rfl⟩
      show (⟨n, hn⟩ : ↥N) * y * ⟨n, hn⟩⁻¹ ∈ centralizer (J : Set ↥N)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : (⟨n, hn⟩ : ↥N)⁻¹ * x * ⟨n, hn⟩ ∈ J := by
        have := (mem_normalizer_iff.mp (hJn (⟨n, hn⟩ : ↥N)⁻¹) x).mp hx
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hy _ hx'
      calc x * (⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹)
          = ⟨n, hn⟩ * ((⟨n, hn⟩⁻¹ * x * ⟨n, hn⟩) * y) * ⟨n, hn⟩⁻¹ := by group
        _ = ⟨n, hn⟩ * (y * (⟨n, hn⟩⁻¹ * x * ⟨n, hn⟩)) * ⟨n, hn⟩⁻¹ := by rw [h1]
        _ = (⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹) * x := by group
    intro n hn
    rw [mem_normalizer_iff]
    intro g
    exact ⟨key n hn g, fun hg => by simpa [mul_assoc] using key n⁻¹ (N.inv_mem hn) _ hg⟩
  have hA₀L : A₀ ≤ L := fun a ha => ⟨⟨a, hA₀N ha⟩, hcent (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hLnA₀ : L ≤ normalizer (A₀ : Set G) := fun l hl =>
    hnormA₀ l (Subgroup.mem_centralizer_singleton_iff.mp (hLz hl)) (hLN hl)
  have hA₀Op : A₀ ≤ Op p L := le_Op_of_normalized hA₀L hLnA₀ hA₀p
  have hOpLN : Op p L ≤ Op p N :=
    le_Op_of_normalized ((Op_le' p L).trans hLN) (normalizer_Op_of_normal hLnorm) (op_isPGroup L)
  have hA₀R : A₀ ≤ Op p N := hA₀Op.trans hOpLN
  have hRne : Op p N ≠ ⊥ := fun hb => hA₀ (le_bot_iff.mp (hb ▸ hA₀R))
  have hNR : normalizer ((Op p N : Subgroup G) : Set G) = N :=
    normalizer_eq_of_normalized9 hC h.coatom hRne (Op_le' p N) (le_normalizer_Op' p N)
  have hRL : Op p N ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hOJ hy, rfl⟩
  have hRz : Op p N ≤ Cen z := hRL.trans hLz
  have hRM : Op p N ≤ M := fun r hr => hC.cen_le (hRz hr)
  set P₀ : Subgroup G := Op p M ⊓ Cen z with hP₀
  have hnormP₀ : ∀ c ∈ Cen z, c ∈ normalizer (P₀ : Set G) := fun c hc =>
    Thm1.mem_normalizer_inf (le_normalizer_Op' p M (hC.cen_le hc))
      (mem_normalizer_centralizer_of_comm (S := {z}) fun s hs => by
        rw [Set.mem_singleton_iff.mp hs]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm)
  have hRnP₀ : Op p N ≤ normalizer (P₀ : Set G) := fun r hr => hnormP₀ r (hRz hr)
  have hP₀p : IsPGroup p ↥P₀ := hC.P_pgroup.to_le inf_le_left
  have hWp : IsPGroup p ↥(P₀ ⊔ Op p N) := hP₀p.to_sup_of_normal_left' (op_isPGroup N) hRnP₀
  have hRW : Op p N = P₀ ⊔ Op p N := by
    refine eq_of_inf_normalizer_le hp hWp le_sup_right ?_
    intro x hx
    obtain ⟨hxW, hxN⟩ := hx
    rw [hNR] at hxN
    have hmul : ((P₀ ⊔ Op p N : Subgroup G) : Set G) = (P₀ : Set G) * (Op p N : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left P₀ (Op p N) hRnP₀
    have hx' : x ∈ (P₀ : Set G) * (Op p N : Set G) := by
      rw [← hmul]
      exact hxW
    obtain ⟨a, ha, r, hr, rfl⟩ := hx'
    have haN : a ∈ N := by
      have := N.mul_mem hxN (N.inv_mem (Op_le' p N hr))
      simpa using this
    have haA₀ : a ∈ A₀ := ⟨⟨ha.1, haN⟩, ha.2⟩
    exact mul_mem (hA₀R haA₀) hr
  have hP₀R : P₀ ≤ Op p N := by
    calc P₀ ≤ P₀ ⊔ Op p N := le_sup_left
      _ = Op p N := hRW.symm
  have hP₀A₀ : P₀ ≤ A₀ := fun x hx => ⟨⟨hx.1, Op_le' p N (hP₀R hx)⟩, hx.2⟩
  have hA₀P₀ : A₀ ≤ P₀ := fun x hx => ⟨hx.1.1, hx.2⟩
  have hP₀ne : P₀ ≠ ⊥ := fun hb => hA₀ (le_bot_iff.mp (hb ▸ hA₀P₀))
  have hHtop : normalizer (P₀ : Set G) ≠ ⊤ :=
    normalizer_ne_top9 hC hP₀ne (inf_le_left.trans (Op_le' p M))
  set JG : Subgroup G := J.map N.subtype with hJG
  have hJGH : JG ≤ normalizer (P₀ : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    have hcj : (j : G) ∈ centralizer (P₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hA₀L (hP₀A₀ hx)
      have h1 := Subgroup.mem_centralizer_iff.mp hy j hj
      rw [← hyx]
      exact (congrArg Subtype.val h1).symm
    exact Subgroup.centralizer_le_normalizer _ hcj
  have hJGq : IsQuasisimple ↥JG :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (J.equivMapOfInjective N.subtype N.subtype_injective)
      hJ.1
  have hzJG : z ∈ JG := ⟨z', hzJ, rfl⟩
  have hLieG : LieModel (↥JG ⧸ center ↥JG) .PSL 3 p n := by
    refine Odd87.Transport.lieModel_of_mulEquiv ?_ hLie
    exact QuotientGroup.congr (center ↥J) (center ↥JG)
      (J.equivMapOfInjective N.subtype N.subtype_injective) (Subgroup.map_center_eq _)
  exact hNo G z k S hC.ctx _ (fun c hc => hnormP₀ c hc) hHtop JG hJGH hJGq hzJG (noc_of_component hJ hO2') p n hp hp2 hn hLieG

end A0

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
