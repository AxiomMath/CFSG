module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.LocalAnalysis.OddStandard.L34FaithfulSL3
public import CFSG.LocalAnalysis.OddStandard.L34FaithfulSeitz

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint

theorem false_of_seitz77Outcome {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L) (h34 : LieModel (L ⧸ center L) .PSL 3 2 2)
    (hout : Seitz77Outcome G L 3 2) : False := by
  have hsimple : IsSimpleGroup G := hS.simple
  have hnab := hS.nonab
  have hCeven : Even (Nat.card (centralizer (L : Set G))) := hS.standard.2.1
  have hO : CFSG.oddCore G = ⊥ := GlueL34.oddCore_eq_bot hS
  have hZ : center G = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  let eQ : G ⧸ center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hQ : IsSimpleGroup (G ⧸ center G) := eQ.isSimpleGroup
  have hQnab : ∃ a b : G ⧸ center G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eQ.symm a, eQ.symm b, fun h => hab (eQ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hlayer : CFSG.layer (G ⧸ center G) = ⊤ :=
    LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => G ⧸ center G)
      (fun _ => hQnab) (MulEquiv.piUnique (fun _ : Unit => G ⧸ center G)).symm
  let eG : G ≃* ↥(CFSG.layer (G ⧸ center G)) :=
    eQ.symm.trans ((MulEquiv.subgroupCongr hlayer).trans Subgroup.topEquiv).symm
  have hcard : Nat.card (L ⧸ center L) = 20160 := GlueL34.card_eq_of_lieModel_psl34 h34
  rcases hout with hN | hii | ⟨X, _, hX, ⟨e⟩⟩
  ·
    rw [hO, bot_sup_eq] at hN
    exact GlueL34.not_normal hS hN
  ·
    rcases hii with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨-, K, hKf, hKfin, hKc, ⟨e⟩⟩ := hcl
      have : Fintype K := Fintype.ofFinite K
      have hK16 : Fintype.card K = 16 := by
        rw [← Nat.card_eq_fintype_card, hKc]
        norm_num
      have hseven : 7 ∣ Nat.card L := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
        rw [hcard] at h1
        rw [h1]
        exact Dvd.dvd.mul_right (by norm_num) _
      have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 hseven
      have hx7 : (x : G) ^ 7 = 1 := by
        rw [← hx, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      have hx1 : (x : G) ≠ 1 := by
        intro h1
        have : x = 1 := Subtype.ext h1
        rw [this, orderOf_one] at hx
        omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, htC, ht2⟩ : ∃ t : G, t ∈ centralizer (L : Set G) ∧ orderOf t = 2 := by
        obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hCeven)
        exact ⟨y, y.2, (Subgroup.orderOf_coe y).trans hy⟩
      have hxt : (x : G) * t = t * (x : G) :=
        Subgroup.mem_centralizer_iff.1 htC (x : G) x.2
      have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
      have := L34Faithful.eq_one_of_commute_order_seven_psl_gf16 hK16 (eG.trans e) hxt hx7 hx1
        ht2'
      rw [this, orderOf_one] at ht2
      omega
    all_goals omega
  ·
    have hXcard : Nat.card X = 20160 := GlueL34.card_eq_of_lieModel_psl34 hX
    have hXnt : Nontrivial X := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have := Nat.card_of_subsingleton (1 : X)
      omega
    obtain ⟨y, hy⟩ := exists_ne (1 : X)
    have hXX : IsSimpleGroup (X × X) := (eG.trans e).symm.isSimpleGroup
    rcases hXX.eq_bot_or_eq_top_of_normal (MonoidHom.ker (MonoidHom.snd X X)) with h | h
    · have : ((y, 1) : X × X) ∈ MonoidHom.ker (MonoidHom.snd X X) :=
        MonoidHom.mem_ker.2 rfl
      rw [h, Subgroup.mem_bot] at this
      exact hy (congrArg Prod.fst this)
    · have : ((1, y) : X × X) ∈ MonoidHom.ker (MonoidHom.snd X X) := by rw [h]; trivial
      exact hy (MonoidHom.mem_ker.1 this)

end CFSG.OddStandard
