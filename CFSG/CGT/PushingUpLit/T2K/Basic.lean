module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.CGT.PushingUpLit.T2K

open scoped commutatorElement

variable {G : Type} [Group G]

theorem perfect_hom_trivial {L : Subgroup G} (hL : ⁅L, L⁆ = L) {Q : Type*} [Group Q]
    (f : ↥L →* Q) (hf : ∀ a b : ↥L, f a * f b = f b * f a) (l : ↥L) : f l = 1 := by
  have hle : L ≤ f.ker.map L.subtype := by
    conv_lhs => rw [← hL]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    refine ⟨⁅(⟨a, ha⟩ : ↥L), (⟨b, hb⟩ : ↥L)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hf _ _)
  obtain ⟨k, hk, hkl⟩ := hle l.2
  have : k = l := Subtype.ext hkl
  rwa [this] at hk

theorem comm_mem_of_perfect {L N K : Subgroup G} (hL : ⁅L, L⁆ = L) (hNL : N ≤ L) (hKN : K ≤ N)
    (hNK : ⁅N, L⁆ ≤ K) {x : G} (h : ∀ l ∈ L, ⁅x, l⁆ ∈ N) (l : G) (hl : l ∈ L) :
    ⁅x, l⁆ ∈ K := by
  classical
  have hNN : ⁅N, N⁆ ≤ K := (Subgroup.commutator_mono le_rfl hNL).trans hNK
  have hnormK : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
    intro n hn k hk
    have h1 : ⁅n, k⁆ ∈ K := hNN (Subgroup.commutator_mem_commutator hn (hKN hk))
    have e : n * k * n⁻¹ = ⁅n, k⁆ * k := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact K.mul_mem h1 hk
  have : (K.subgroupOf N).Normal :=
    ⟨fun k hk n => by
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      simpa using hnormK n n.2 k hk⟩
  let f : ↥L →* ↥N ⧸ K.subgroupOf N :=
    MonoidHom.mk' (fun a => QuotientGroup.mk (⟨⁅x, (a : G)⁆, h a a.2⟩ : ↥N)) (fun a b => by
      have hb : ⁅x, (b : G)⁆ ∈ N := h b b.2
      have key : ⁅x, (a : G) * b⁆ = ⁅x, (a : G)⁆ * ((a : G) * ⁅x, (b : G)⁆ * (a : G)⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hmem : ⁅⁅x, (b : G)⁆⁻¹, (a : G)⁆ ∈ K :=
        hNK (Subgroup.commutator_mem_commutator (N.inv_mem hb) a.2)
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : (⁅x, (a : G) * b⁆)⁻¹ * (⁅x, (a : G)⁆ * ⁅x, (b : G)⁆) =
          (⁅⁅x, (b : G)⁆⁻¹, (a : G)⁆)⁻¹ := by
        rw [key]
        simp only [commutatorElement_def]
        group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      exact K.inv_mem hmem)
  have hcomm : ∀ p q : ↥N ⧸ K.subgroupOf N, p * q = q * p := by
    intro p q
    refine QuotientGroup.induction_on p fun p => QuotientGroup.induction_on q fun q => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have e : (((p * q)⁻¹ * (q * p) : ↥N) : G) = ⁅(q : G)⁻¹, (p : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hNN (Subgroup.commutator_mem_commutator (N.inv_mem q.2) (N.inv_mem p.2))
  have h1 := perfect_hom_trivial hL f (fun a b => hcomm _ _) ⟨l, hl⟩
  have h2 : (⟨⁅x, l⁆, h l hl⟩ : ↥N) ∈ K.subgroupOf N := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

theorem comm_eq_one_of_perfect {L : Subgroup G} (hL : ⁅L, L⁆ = L) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ l ∈ L, ⁅x, l⁆ ∈ Subgroup.centralizer (L : Set G)) (l : G) (hl : l ∈ L) :
    ⁅x, l⁆ = 1 := by
  have hN : ∀ l ∈ L, ⁅x, l⁆ ∈ L ⊓ Subgroup.centralizer (L : Set G) := by
    intro l hl
    refine Subgroup.mem_inf.2 ⟨?_, h l hl⟩
    have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hx l).1 hl
    have e : ⁅x, l⁆ = (x * l * x⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hNK : ⁅L ⊓ Subgroup.centralizer (L : Set G), L⁆ ≤ ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.2 inf_le_right).le
  have := comm_mem_of_perfect hL inf_le_left bot_le hNK hN l hl
  exact Subgroup.mem_bot.1 this

end CFSG.CGT.PushingUpLit.T2K
