module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Def
public import CFSG.CGT.PushingUpLit.LIT.A4.L34Main
public import CFSG.CGT.PushingUpLit.LIT.A4.Unique

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.RankThree.PartOne.SolD3 (Blk3)
open scoped commutatorElement

namespace L34

variable {G : Type} [Group G]

@[expose] def twoOf (M X : Subgroup G) (m a : G) : Two G :=
  ⟨M, X, conjSub m X, a, m * a * m⁻¹⟩

theorem centralizer_single_le_zpowers (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  have hcz : Commute c z := Subgroup.mem_centralizer_singleton_iff.1 hc
  exact (hcz.zpow_right n).symm.eq

variable [Finite G] {M X : Subgroup G}

theorem cent_of_a4cfg (c : A4Cfg G M X) {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1) {k : G}
    (hk : k ∈ M) (hzk : ∀ x ∈ conjSub k X, z * x = x * z) :
    Subgroup.centralizer ({z} : Set G) ≤ M := by
  have hord : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hP : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  have hP1 : Subgroup.zpowers z ≠ ⊥ := fun e => hz1 (Subgroup.zpowers_eq_bot.1 e)
  have hzc : z ∈ Subgroup.centralizer ((conjSub k X : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hzk x hx).symm
  have hPX : Subgroup.zpowers z ≤ Subgroup.centralizer ((conjSub k X : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 hzc
  exact le_trans (centralizer_single_le_zpowers z) (c.centralizer_le hP hP1 hk hPX)

theorem cfg_twoOf (c : A4Cfg G M X) {m : G} (h2 : TwoConj M X m) {a : G} (ha : Blk3 X a) :
    (twoOf M X m a).Cfg where
  blk₁ := ha
  blk₂ := Blk3.conj ha m
  le₁ := c.le
  le₂ := c.conj_le h2.1
  comm := by
    intro x hx y hy
    have hcomm := c.commutator_conj_eq_bot h2.1 h2.2.1
    have h1 : ⁅x, y⁆ ∈ ⁅X, conjSub m X⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 h1)
  perm := by
    intro k hk
    have hkm : k * m ∈ M := M.mul_mem hk h2.1
    have hXne : conjSub m X ≠ X := h2.2.1
    have inj := conjSub_injective (G := G) k
    have e : conjSub k (conjSub m X) = conjSub (k * m) X := conjSub_conjSub k m X
    show (conjSub k X = X ∧ conjSub k (conjSub m X) = conjSub m X) ∨
      (conjSub k X = conjSub m X ∧ conjSub k (conjSub m X) = X)
    rcases h2.2.2 k hk with e1 | e1
    · left
      refine ⟨e1, ?_⟩
      rcases h2.2.2 (k * m) hkm with e2 | e2
      · exfalso
        apply hXne
        apply inj
        rw [e, e2, e1]
      · rw [e, e2]
    · right
      refine ⟨e1, ?_⟩
      rcases h2.2.2 (k * m) hkm with e2 | e2
      · rw [e, e2]
      · exfalso
        apply hXne
        apply inj
        rw [e, e2, e1]
  swap := ⟨m, h2.1, rfl⟩
  cent := by
    intro z hz1 hz2 hz
    rcases hz with hz | hz
    · exact cent_of_a4cfg c hz1 hz2 M.one_mem (by rw [conjSub_one]; exact hz)
    · exact cent_of_a4cfg c hz1 hz2 h2.1 hz

theorem hle₂_twoOf (c : A4Cfg G M X) {m : G} (h2 : TwoConj M X m) :
    ∀ g, conjSub g (conjSub m X) ≤ M → g ∈ M := by
  intro g hg
  rw [conjSub_conjSub] at hg
  exact (M.mul_mem_cancel_right h2.1).1 (c.mem_of_conj_le hg)

theorem hnorm_twoOf (c : A4Cfg G M X) {m : G} (h2 : TwoConj M X m) {a : G} (ha : Blk3 X a) :
    Subgroup.normalizer (((twoOf M X m a).A : Subgroup G) : Set G) ≤ M := by
  have hcfg := cfg_twoOf c h2 ha
  refine c.normalizer_le (m := 1) ?_ ?_ M.one_mem ?_
  · intro x
    refine ⟨1, Subtype.ext ?_⟩
    have := hcfg.A_sq x.2
    simpa [pow_two] using this
  · intro e
    obtain ⟨w, hw, hw1⟩ := ha.exists_ne_one
    have hwA : w ∈ (twoOf M X m a).A := (twoOf M X m a).V₁_le_A hw
    rw [e] at hwA
    exact hw1 (Subgroup.mem_bot.1 hwA)
  · rw [conjSub_one]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨fun hz => hcfg.X₁_conj_A hx hz, fun hz => by
      have := hcfg.X₁_conj_A (X.inv_mem hx) hz
      simpa [mul_assoc] using this⟩

end L34

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G}

theorem strongClosureTwo (c : A4Cfg G M X) {m : G} (h2 : TwoConj M X m) :
    StrongClosureTwo M X m := by
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.SolD3.exists_blk3 c.short c.nat
  exact (L34.cfg_twoOf c h2 ha).sc (fun g hg => c.mem_of_conj_le hg) (L34.hle₂_twoOf c h2)
    (L34.hnorm_twoOf c h2 ha)

theorem lemma34Two (c : A4Cfg G M X) {m : G} (h2 : TwoConj M X m) : Lemma34Two M := by
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.SolD3.exists_blk3 c.short c.nat
  intro U hUM hU g hC
  exact (L34.cfg_twoOf c h2 ha).lemma34 (fun g hg => c.mem_of_conj_le hg) (L34.hle₂_twoOf c h2)
    (L34.hnorm_twoOf c h2 ha) hUM hU hC

end CFSG.CGT.PushingUpLit.A4
