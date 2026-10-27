module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Rep
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Num
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Plane
import CFSG.RankThree.PartOne.K1327.Trick

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG.Open CFSG.LocalAnalysis.NilpotentFrattiniAction Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal] [Fact (IsPGroup 2 Q)]

abbrev Rsub (T : Subgroup G) (z x : G) : Subgroup G :=
  ⁅zpowers z, T ⊓ centralizer ({x} : Set G)⁆

noncomputable def Sb (b : G) : Submodule (ZMod 2) (FV Q) :=
  subV Q ((Q ⊓ centralizer ({b} : Set G)).subgroupOf Q)

noncomputable def Ub (z b : G) : Submodule (ZMod 2) (FV Q) :=
  (Sb Q b).map (rep Q z - 1)

theorem mem_Sb {b : G} {v : FV Q} :
    v ∈ Sb Q b ↔ ∃ c : ↥Q, (c : G) ∈ centralizer ({b} : Set G) ∧ piV Q c = v := by
  unfold Sb
  rw [mem_subV]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, (Subgroup.mem_subgroupOf.1 hc).2, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, Subgroup.mem_subgroupOf.2 ⟨c.2, hc⟩, h⟩

theorem Sb_mono {b b' : G} (h : centralizer ({b} : Set G) ≤ centralizer ({b'} : Set G)) :
    Sb Q b ≤ Sb Q b' := by
  intro v hv
  obtain ⟨c, hc, rfl⟩ := (mem_Sb Q).1 hv
  exact (mem_Sb Q).2 ⟨c, h hc, rfl⟩

theorem Ub_mono (z : G) {b b' : G}
    (h : centralizer ({b} : Set G) ≤ centralizer ({b'} : Set G)) : Ub Q z b ≤ Ub Q z b' :=
  Submodule.map_mono (Sb_mono Q h)

theorem centralizer_le_of_mem_zpowers {b y : G} (hy : y ∈ zpowers b) :
    centralizer ({b} : Set G) ≤ centralizer ({y} : Set G) := by
  intro c hc
  rw [mem_centralizer_singleton_iff] at hc ⊢
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact (Commute.zpow_right (show Commute c b from hc) k).eq

theorem rep_sub_one_piV (z : G) (c : ↥Q) :
    ∃ d : ↥Q, (d : G) = z * (c : G) * z⁻¹ * (c : G)⁻¹ ∧
      (rep Q z - 1) (piV Q c) = piV Q d := by
  refine ⟨MulAut.conjNormal z c * c⁻¹, ?_, rep_sub_one_apply Q z c⟩
  simp [MulAut.conjNormal_apply, mul_assoc]

theorem Ub_eq_bot {z b : G} (h : centralizer ({b} : Set G) ≤ centralizer ({z} : Set G)) :
    Ub Q z b = ⊥ := by
  rw [Ub, eq_bot_iff]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨c, hc, rfl⟩ := (mem_Sb Q).1 hw
  obtain ⟨d, hd, hd'⟩ := rep_sub_one_piV Q z c
  have hzc : (c : G) * z = z * (c : G) := mem_centralizer_singleton_iff.mp (h hc)
  have hd1 : d = 1 := by
    apply Subtype.ext
    rw [hd, Subgroup.coe_one]
    calc z * (c : G) * z⁻¹ * (c : G)⁻¹ = (c : G) * z * z⁻¹ * (c : G)⁻¹ := by rw [hzc]
      _ = 1 := by group
  rw [hd', hd1]
  exact (Submodule.mem_bot (ZMod 2)).2 (piV_one Q)

theorem Ub_le_subV {T : Subgroup G} (hQT : Q ≤ T) (z x : G) :
    Ub Q z x ≤ subV Q
      ((Rsub T z x ⊓ Q).subgroupOf Q) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨c, hc, rfl⟩ := (mem_Sb Q).1 hw
  obtain ⟨d, hd, hd'⟩ := rep_sub_one_piV Q z c
  rw [LinearMap.sub_apply, ← LinearMap.sub_apply, hd']
  refine (mem_subV Q).2 ⟨d, Subgroup.mem_subgroupOf.2 ⟨?_, d.2⟩, rfl⟩
  have hcom : ⁅z, (c : G)⁆ ∈ Rsub T z x :=
    Subgroup.commutator_mem_commutator (mem_zpowers z) ⟨hQT c.2, hc⟩
  rwa [commutatorElement_def, ← hd] at hcom

theorem Ub_le_map_of_conj {z x y g : G} (hg : g * z = z * g)
    (hgx : g * x * g⁻¹ ∈ zpowers y) : Ub Q z y ≤ (Ub Q z x).map (rep Q g) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨c, hc, rfl⟩ := (mem_Sb Q).1 hw
  set c₀ : ↥Q := MulAut.conjNormal g⁻¹ c with hc₀
  have hc₀G : (c₀ : G) = g⁻¹ * (c : G) * g := by
    rw [hc₀, MulAut.conjNormal_apply]
    simp
  have hcy : (c : G) * (g * x * g⁻¹) = (g * x * g⁻¹) * (c : G) := by
    have h1 := centralizer_le_of_mem_zpowers hgx hc
    exact mem_centralizer_singleton_iff.mp h1
  have hc₀x : (c₀ : G) ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff, hc₀G]
    calc g⁻¹ * (c : G) * g * x = g⁻¹ * ((c : G) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (c : G)) * g := by rw [hcy]
      _ = x * (g⁻¹ * (c : G) * g) := by group
  have hcc : MulAut.conjNormal g c₀ = c := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hc₀G]
    group
  have hw₀ : piV Q c₀ ∈ Sb Q x := (mem_Sb Q).2 ⟨c₀, hc₀x, rfl⟩
  refine ⟨(rep Q z - 1) (piV Q c₀), ⟨_, hw₀, rfl⟩, ?_⟩
  have hcomm : rep Q g * rep Q z = rep Q z * rep Q g := by
    rw [← map_mul, ← map_mul, hg]
  have hpi : piV Q c = rep Q g (piV Q c₀) := by rw [rep_apply, hcc]
  rw [hpi]
  have h3 : (rep Q z - 1) (rep Q g (piV Q c₀)) =
      rep Q z (rep Q g (piV Q c₀)) - rep Q g (piV Q c₀) := by
    simp
  have h4 : rep Q g ((rep Q z - 1) (piV Q c₀)) =
      rep Q g (rep Q z (piV Q c₀)) - rep Q g (piV Q c₀) := by
    simp
  rw [h3, h4]
  have h5 : rep Q z (rep Q g (piV Q c₀)) = rep Q g (rep Q z (piV Q c₀)) :=
    (LinearMap.congr_fun hcomm (piV Q c₀)).symm
  rw [h5]

theorem finrank_Ub_le_four_x {T : Subgroup G} (hQT : Q ≤ T) {z x : G}
    (hR32 : Nat.card (Rsub T z x) ≤ 32) (hsq : ∃ r ∈ Rsub T z x, r ^ 2 ≠ 1) :
    Module.finrank (ZMod 2) (Ub Q z x) ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥Q := Fact.out
  have hE : ∀ e : ↥Q ⧸ frattini ↥Q, e ^ 2 = 1 :=
    (CFSG.GroupTheory.frattini_elementary_quotient hQ).2.2.1
  have hcard := card_map_le_sixteen hE hR32 hsq (QuotientGroup.mk' (frattini ↥Q))
  refine (Submodule.finrank_mono (Ub_le_subV Q hQT z x)).trans ?_
  refine finrank_le_of_card_le Q ?_
  rw [card_subV]
  exact hcard.trans (by norm_num)

theorem finrank_Ub_le_four {P : Sylow 5 G} {x z y : G} {T : Subgroup G}
    (hB : SmallRankPlane 5 (P : Subgroup G) x z)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (h4 : 4 ≤ Open.pRank 5 (P : Subgroup G)) (hQT : Q ≤ T)
    (hR32 : Nat.card (Rsub T z x) ≤ 32) (hsq : ∃ r ∈ Rsub T z x, r ^ 2 ≠ 1)
    (hyB : y ∈ zpowers x ⊔ zpowers z) (hyZ : y ∉ zpowers z) :
    Module.finrank (ZMod 2) (Ub Q z y) ≤ 4 := by
  obtain ⟨g, hg, hgx⟩ := exists_conj_line (by norm_num) hB hzc h4 hyB hyZ
  have hgz : g * z = z * g := mem_centralizer_iff.mp hzc g hg.1
  have hgx' : g * x * g⁻¹ ∈ zpowers y := by
    have h1 : (MulAut.conj g).toMonoidHom x ∈ (zpowers x).map (MulAut.conj g).toMonoidHom :=
      mem_map_of_mem _ (mem_zpowers x)
    rw [hgx] at h1
    simpa [MulAut.conj_apply] using h1
  calc Module.finrank (ZMod 2) (Ub Q z y)
      ≤ Module.finrank (ZMod 2) ((Ub Q z x).map (rep Q g)) :=
        Submodule.finrank_mono (Ub_le_map_of_conj Q hgz hgx')
    _ ≤ Module.finrank (ZMod 2) (Ub Q z x) := Submodule.finrank_map_le _ _
    _ ≤ 4 := finrank_Ub_le_four_x Q hQT hR32 hsq

theorem finrank_range_le_twenty {P : Sylow 5 G} {x z : G} {T : Subgroup G}
    (hB : SmallRankPlane 5 (P : Subgroup G) x z)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (h4 : 4 ≤ Open.pRank 5 (P : Subgroup G)) (hQT : Q ≤ T)
    (hR32 : Nat.card (Rsub T z x) ≤ 32) (hsq : ∃ r ∈ Rsub T z x, r ^ 2 ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (rep Q z - 1)) ≤ 20 := by
  classical
  have hp5 : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp5⟩
  obtain ⟨hxP, hzP, hxp, hzp, hx1, hz1⟩ := plane_facts hp5 hB
  have hQ : IsPGroup 2 ↥Q := Fact.out
  have hQcop : ¬ 5 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow hp5 h
    omega
  have hBQ : (zpowers x ⊔ zpowers z : Subgroup G) ≤ normalizer (Q : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hgen := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers hp5 hB.isElemAbelian
    hB.card_eq hBQ hQcop
  have htop : (⊤ : Subgroup ↥Q) ≤
      ⨆ b : {b : ↥(zpowers x ⊔ zpowers z : Subgroup G) // b ≠ 1},
        (Q ⊓ centralizer ({(b.1 : G)} : Set G)).subgroupOf Q := by
    have hmap : (⨆ b : {b : ↥(zpowers x ⊔ zpowers z : Subgroup G) // b ≠ 1},
        (Q ⊓ centralizer ({(b.1 : G)} : Set G)).subgroupOf Q).map Q.subtype =
        ⨆ b : {b : ↥(zpowers x ⊔ zpowers z : Subgroup G) // b ≠ 1},
          Q ⊓ centralizer ({(b.1 : G)} : Set G) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun b => Subgroup.map_subgroupOf_eq_of_le inf_le_left
    rw [← Subgroup.map_le_map_iff_of_injective Q.subtype_injective, hmap,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have hS : (⊤ : Submodule (ZMod 2) (FV Q)) ≤
      ⨆ b : {b : ↥(zpowers x ⊔ zpowers z : Subgroup G) // b ≠ 1}, Sb Q (b.1 : G) := by
    rw [← subV_top Q]
    exact (subV_mono Q htop).trans (le_of_eq (subV_iSup Q _))
  have hrange : LinearMap.range (rep Q z - 1) ≤
      ⨆ b : {b : ↥(zpowers x ⊔ zpowers z : Subgroup G) // b ≠ 1}, Ub Q z (b.1 : G) := by
    rw [LinearMap.range_eq_map]
    refine (Submodule.map_mono hS).trans ?_
    rw [Submodule.map_iSup]
    exact le_rfl
  set y : Fin 5 → G := fun j => x * z ^ (j : ℕ) with hy
  have hle : LinearMap.range (rep Q z - 1) ≤ ⨆ j : Fin 5, Ub Q z (y j) := by
    refine hrange.trans (iSup_le fun b => ?_)
    have hbB : (b.1 : G) ∈ zpowers x ⊔ zpowers z := b.1.2
    have hb1 : (b.1 : G) ≠ 1 := fun h => b.2 (Subtype.ext h)
    by_cases hbz : (b.1 : G) ∈ zpowers z
    · have hbp : (b.1 : G) ^ 5 = 1 := hB.isElemAbelian.2 _ hbB
      have hzb : zpowers (b.1 : G) = zpowers z := by
        refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hbz) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hbp hb1,
          orderOf_eq_prime hzp hz1]
      have hzmem : z ∈ zpowers (b.1 : G) := by rw [hzb]; exact mem_zpowers z
      rw [Ub_eq_bot Q (centralizer_le_of_mem_zpowers hzmem)]
      exact bot_le
    · obtain ⟨j, hj⟩ := exists_line_rep hp5 hB hzc hbB hbz
      exact (Ub_mono Q z (centralizer_le_of_mem_zpowers hj)).trans
        (le_iSup (fun j => Ub Q z (y j)) j)
  have hxz : x ∉ zpowers z := by
    intro h
    have h1 : (zpowers x ⊔ zpowers z : Subgroup G) = zpowers z :=
      sup_eq_right.mpr (zpowers_le.mpr h)
    have h2 := hB.card_eq
    rw [h1, Nat.card_zpowers, orderOf_eq_prime hzp hz1] at h2
    norm_num at h2
  have hy4 : ∀ j : Fin 5, Module.finrank (ZMod 2) (Ub Q z (y j)) ≤ 4 := by
    intro j
    refine finrank_Ub_le_four Q hB hzc h4 hQT hR32 hsq ?_ ?_
    · exact mul_mem (mem_sup_left (mem_zpowers x)) (pow_mem (mem_sup_right (mem_zpowers z)) _)
    · intro hyz
      apply hxz
      have hyz' : x * z ^ (j : ℕ) ∈ zpowers z := hyz
      have := mul_mem hyz' (inv_mem (pow_mem (mem_zpowers z) (j : ℕ)))
      simpa using this
  calc Module.finrank (ZMod 2) (LinearMap.range (rep Q z - 1))
      ≤ Module.finrank (ZMod 2) (⨆ j : Fin 5, Ub Q z (y j) : Submodule (ZMod 2) (FV Q)) :=
        Submodule.finrank_mono hle
    _ = Module.finrank (ZMod 2)
        (Finset.univ.sup fun j : Fin 5 => Ub Q z (y j) : Submodule (ZMod 2) (FV Q)) := by
        rw [Finset.sup_univ_eq_iSup]
    _ ≤ ∑ j : Fin 5, Module.finrank (ZMod 2) (Ub Q z (y j)) := finrank_finset_sup_le _ _
    _ ≤ ∑ _j : Fin 5, 4 := Finset.sum_le_sum fun j _ => hy4 j
    _ = 20 := by simp

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65
