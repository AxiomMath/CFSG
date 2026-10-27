module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerQuasi
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

section Index

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem mem_of_sq_mem_of_pow_eq_one (hp2 : p ≠ 2) (hp : p.Prime) (J : Subgroup G)
    (hJ : ∀ g : G, g ^ 2 ∈ J) {x : G} {k : ℕ} (hx : x ^ p ^ k = 1) : x ∈ J := by
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have : x = (x ^ 2) ^ (m + 1) := by
    calc x = x ^ p ^ k * x := by rw [hx, one_mul]
      _ = x ^ (p ^ k + 1) := by rw [pow_succ]
      _ = x ^ (2 * (m + 1)) := by rw [hm]; ring_nf
      _ = (x ^ 2) ^ (m + 1) := by rw [pow_mul]
  rw [this]
  exact J.pow_mem (hJ x) _

theorem oddPCoreInClosure_of_sq_mem (hp : p.Prime) (hp2 : p ≠ 2) (J : Subgroup G) [J.Normal]
    (hJ : ∀ g : G, g ^ 2 ∈ J) (h : OddPCoreInClosure p ↥J) : OddPCoreInClosure p G := by
  intro K hK hKle hKcop
  have hmap : pElemClosure p G = (pElemClosure p ↥J).map J.subtype := by
    rw [pElemClosure, pElemClosure, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨⟨x, mem_of_sq_mem_of_pow_eq_one hp2 hp J hJ hk⟩, ⟨k, Subtype.ext hk⟩, rfl⟩
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hKJ : K ≤ J := by
    refine hKle.trans ?_
    rw [hmap]
    exact Subgroup.map_subtype_le _
  haveI : (K.subgroupOf J).Normal := Subgroup.Normal.subgroupOf hK J
  have hle : K.subgroupOf J ≤ pElemClosure p ↥J := by
    intro y hy
    have hyK : (y : G) ∈ K := hy
    have : (y : G) ∈ (pElemClosure p ↥J).map J.subtype := hmap ▸ hKle hyK
    obtain ⟨z, hz, hzy⟩ := this
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz
  have hcard : Nat.card (K.subgroupOf J) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv
  have := h (K.subgroupOf J) inferInstance hle (hcard ▸ hKcop)
  rwa [hcard] at this

theorem oddPCoreInClosure_of_hom (hp : p.Prime) (hp2 : p ≠ 2) (φ : G →* Multiplicative (ZMod 2))
    (hker : ∀ x : G, φ x = 1 → x ^ 2 = 1 → x = 1) : OddPCoreInClosure p G := by
  intro K hK hKle hKcop
  have hodd : ∀ x : G, ∀ k : ℕ, x ^ p ^ k = 1 → φ x = 1 := by
    intro x k hx
    have h1 : φ x ^ p ^ k = 1 := by rw [← map_pow, hx, map_one]
    have h2 : φ x ^ 2 = 1 := by
      have hall : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by decide
      exact hall (φ x)
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have hd : orderOf (φ x) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hd' : orderOf (φ x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd hd'))
  have hKker : K ≤ φ.ker := by
    refine hKle.trans ?_
    rw [pElemClosure, Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    exact hodd x k hk
  refine odd_natCard_of_forall_sq fun x hx2 => ?_
  have hx2' : (x : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hx2
  exact Subtype.ext (hker x (MonoidHom.mem_ker.1 (hKker x.2)) hx2')

end Index

theorem oddPCoreInClosure_of_isQuasisimple {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (hJ : CFSG.IsQuasisimple J) (hcen : Odd (Nat.card (Subgroup.center J))) :
    OddPCoreInClosure p J := by
  have hQ : CFSG.IsQuasisimple ↥(⊤ : Subgroup J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hJ
  refine oddPCoreInClosure_of_quasisimple_normal hp ⊤ hQ ?_ ?_
  · rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    exact hcen
  · intro h
    rw [Subgroup.card_top]
    exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
