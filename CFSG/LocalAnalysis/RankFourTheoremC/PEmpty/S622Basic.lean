module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo smallRankS smallRankR smallRankD
  IsMaxTwoInvariantIn IsTwoInvariantIn exists_isMaxTwoInvariantIn_of_le)
open scoped commutatorElement

structure S622Conf {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x z : G) (T S : Subgroup G) : Prop where
  config : S62Config p P M x z T
  isMax : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)) S
  le_S : smallRankS x T ≤ S

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S : Subgroup G}

namespace S622Conf

theorem S_le_centralizer (c : S622Conf p P M x z T S) : S ≤ centralizer ({x} : Set G) :=
  c.isMax.1.1

theorem S_isPGroup (c : S622Conf p P M x z T S) : IsPGroup 2 S := c.isMax.1.2.1

theorem B_le_normalizer (c : S622Conf p P M x z T S) :
    zpowers x ⊔ zpowers z ≤ normalizer (S : Set G) := c.isMax.1.2.2

theorem z_le_normalizer (c : S622Conf p P M x z T S) :
    zpowers z ≤ normalizer (S : Set G) := le_sup_right.trans c.B_le_normalizer

theorem normalizer_le_of_invariant (c : S62Config p P M x z T) {W : Subgroup G}
    (hW2 : IsPGroup 2 W) (hW1 : W ≠ ⊥) (hWM : W ≤ M)
    (hBW : zpowers x ⊔ zpowers z ≤ normalizer (W : Set G)) : normalizer (W : Set G) ≤ M :=
  c.prop614 (normalizer (W : Set G)) ⟨W, hW1, hW2, rfl⟩ hBW
    ⟨W, le_inf le_normalizer hWM, hW1, hW2, hBW⟩

theorem S_le_M (c : S622Conf p P M x z T S) : S ≤ M := by
  refine le_of_inf_ne_bot c.config.prop614 c.config.B_le_M c.S_isPGroup c.B_le_normalizer ?_
  intro h
  apply c.config.S_ne_bot
  rw [eq_bot_iff]
  exact (le_inf c.le_S c.config.S_le_M).trans h.le

theorem B_le_normalizer_of_z (c : S622Conf p P M x z T S) {W : Subgroup G}
    (hWC : W ≤ centralizer ({x} : Set G)) (hz : zpowers z ≤ normalizer (W : Set G)) :
    zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) := by
  refine sup_le ?_ hz
  rw [zpowers_le]
  exact Subgroup.centralizer_le_normalizer (W : Set G) (mem_centralizer_iff.mpr fun h hh =>
    (mem_centralizer_singleton_iff.mp (hWC hh)))

theorem normalizer_le (c : S622Conf p P M x z T S) {S₀ : Subgroup G} (hS₀S : S₀ ≤ S)
    (hS₀1 : S₀ ≠ ⊥) (hz : zpowers z ≤ normalizer (S₀ : Set G)) :
    normalizer (S₀ : Set G) ≤ M :=
  normalizer_le_of_invariant c.config (c.S_isPGroup.to_le hS₀S) hS₀1 (hS₀S.trans c.S_le_M)
    (c.B_le_normalizer_of_z (hS₀S.trans c.S_le_centralizer) hz)

theorem R_le_S (c : S622Conf p P M x z T S) : ⁅zpowers z, S⁆ ≤ S := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have hanorm : a ∈ normalizer (S : Set G) := c.z_le_normalizer ha
  have h1 : a * b * a⁻¹ ∈ S := (mem_normalizer_iff.mp hanorm b).mp hb
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hb)

theorem z_le_normalizer_R (c : S622Conf p P M x z T S) :
    zpowers z ≤ normalizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G) := by
  rw [zpowers_le, mem_normalizer_iff_map_conj_eq]
  have hzS : S.map (MulAut.conj z).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (c.z_le_normalizer (mem_zpowers z))
  have hzz : (zpowers z).map (MulAut.conj z).toMonoidHom = zpowers z := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have h := Subgroup.map_commutator (H₁ := zpowers z) (H₂ := S) (MulAut.conj z).toMonoidHom
  rw [hzS, hzz] at h
  exact h

theorem R_ne_bot (c : S622Conf p P M x z T S) : ⁅zpowers z, S⁆ ≠ ⊥ := by
  intro h
  apply c.config.R_ne_bot
  rw [eq_bot_iff]
  exact (Subgroup.commutator_mono le_rfl c.le_S).trans h.le

theorem R_isPGroup (c : S622Conf p P M x z T S) : IsPGroup 2 (⁅zpowers z, S⁆ : Subgroup G) :=
  c.S_isPGroup.to_le c.R_le_S

end S622Conf

theorem exists_s622Conf (c : S62Config p P M x z T) : ∃ S : Subgroup G, S622Conf p P M x z T S := by
  have hinv : IsTwoInvariantIn (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G))
      (smallRankS x T) := ⟨inf_le_right, c.S_isPGroup, c.B_le_normalizer_S⟩
  obtain ⟨S, hle, hmax⟩ := exists_isMaxTwoInvariantIn_of_le hinv
  exact ⟨S, ⟨c, hmax, hle⟩⟩

theorem s622_centralizer_ne_top (hS : Situation G p P M) (hx : Point P M x) :
    centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := hS.simple
  have hc : x ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({x} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact hx.ne_one hS.prime (by simpa [h] using hc)
  · obtain ⟨b, c, hbc⟩ := hS.nonab
    exact hbc (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) c).symm

theorem s622_isKGroup_centralizer (hS : Situation G p P M) (hx : Point P M x) :
    CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G)) := by
  have : IsSimpleGroup G := hS.simple
  exact CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper _
      (s622_centralizer_ne_top hS hx))

theorem s622_isKGroup_primeCore (hS : Situation G p P M) (hx : Point P M x) :
    CFSG.Open.IsKGroup ↥(smallRankD p x) := by
  have : IsSimpleGroup G := hS.simple
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hDne : smallRankD p x ≠ ⊤ := fun h => s622_centralizer_ne_top hS hx (top_le_iff.mp
    (h ▸ (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p _ |>.1 :
      smallRankD p x ≤ centralizer ({x} : Set G))))
  exact CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper _ hDne)

theorem s622_x_not_mem_zpowers (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) :
    x ∉ zpowers z := by
  intro hxz
  have hpl := plane_of_central hS hx hz
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hBc := hpl.card_eq
  have hsup : zpowers x ⊔ zpowers z = zpowers z := sup_eq_right.mpr (zpowers_le.mpr hxz)
  rw [hsup, Nat.card_zpowers, orderOf_eq_prime hz.pow_eq_one hz.ne_one] at hBc
  have hp2 := hprime.two_le
  nlinarith [pow_two p]

theorem s622_primeCore_two_eq_of_odd {D : Subgroup G} (hD : Odd (Nat.card D)) :
    rankThreePrimeCore 2 D = D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D).1 ?_
  refine le_sSup ⟨le_rfl, ?_, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · exact Nat.coprime_two_left.mpr hD

theorem s622_zpowers_le_normalizer_of_le_centralizer {W : Subgroup G}
    (hW : W ≤ centralizer ({z} : Set G)) : zpowers z ≤ normalizer (W : Set G) := by
  rw [zpowers_le]
  exact Subgroup.centralizer_le_normalizer (W : Set G) (mem_centralizer_iff.mpr fun h hh =>
    (mem_centralizer_singleton_iff.mp (hW hh)))

theorem s622_card_coprime_odd {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) (hp : p.Prime)
    {F F' : Subgroup G} (hF : IsPGroup f F) (hle : F' ≤ F) :
    Nat.Coprime p (Nat.card F') ∧ Odd (Nat.card F') := by
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨k, hk⟩ := hF.exists_card_eq
  have hdvd : Nat.card F' ∣ f ^ k := hk ▸ Subgroup.card_dvd_of_le hle
  refine ⟨Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right k
    ((Nat.coprime_primes hp hf).mpr hfp.symm)), ?_⟩
  exact Odd.of_dvd_nat ((Nat.Prime.odd_of_ne_two hf hf2).pow) hdvd

theorem s622_le_sup_of_hasNormalPComplement {q : ℕ} (hq : q.Prime) {H Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q H) (h : CFSG.HasNormalPComplement q ↥H) :
    H ≤ Q ⊔ rankThreePrimeCore q H := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨N, hNn, hNcop, hNq⟩ := h
  obtain ⟨Q', hQ'⟩ := hQ.exists_sylow_eq_subgroupOf
  have hidxN : (N ⊔ (Q' : Subgroup ↥H)).index ∣ Nat.card (↥H ⧸ N) :=
    Subgroup.index_dvd_of_le le_sup_left
  have hidxQ : (N ⊔ (Q' : Subgroup ↥H)).index ∣ (Q' : Subgroup ↥H).index :=
    Subgroup.index_dvd_of_le le_sup_right
  obtain ⟨a, ha⟩ := hNq.exists_card_eq
  have hcop : Nat.Coprime (N ⊔ (Q' : Subgroup ↥H)).index (Q' : Subgroup ↥H).index := by
    refine Nat.Coprime.coprime_dvd_left (ha ▸ hidxN) ?_
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hq).mpr Q'.not_dvd_index)
  have hone : (N ⊔ (Q' : Subgroup ↥H)).index = 1 := Nat.Coprime.eq_one_of_dvd hcop hidxQ
  have htop : N ⊔ (Q' : Subgroup ↥H) = ⊤ := Subgroup.index_eq_one.mp hone
  have hmap : (N ⊔ (Q' : Subgroup ↥H)).map H.subtype = H := by
    rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  rw [Subgroup.map_sup] at hmap
  have hQmap : (Q' : Subgroup ↥H).map H.subtype = Q := by
    have := congrArg (Subgroup.map H.subtype) hQ'
    rw [Subgroup.map_subgroupOf_eq_of_le hQ.le] at this
    exact this
  have hN'H : N.map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hN'n : ((N.map H.subtype).subgroupOf H).Normal := by
    have h1 : (N.map H.subtype).subgroupOf H = N :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
    rw [h1]
    exact hNn
  have hN'D : N.map H.subtype ≤ rankThreePrimeCore q H := by
    refine le_sSup ⟨hN'H, hN'n, ?_⟩
    rwa [Subgroup.card_map_of_injective H.subtype_injective]
  rw [hQmap] at hmap
  refine hmap.ge.trans ?_
  rw [sup_comm]
  exact sup_le_sup_left hN'D Q

theorem s622_cover_of_hasNormalPComplement (hS : Situation G p P M) (hx : Point P M x)
    (h : CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G))) :
    centralizer ({x} : Set G) ≤ (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x :=
  (s622_le_sup_of_hasNormalPComplement hS.prime hx.sylow h).trans
    (sup_le_sup_right (inf_le_inf_right _ hS.sylow_le) _)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
