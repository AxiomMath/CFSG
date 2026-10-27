module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgThm
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31Two
import CFSG.GH74.AS16.Standard
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Comps

variable {G : Type} [Group G]

theorem quasisimple_of_isCompIn {H J : Subgroup G} (hJ : IsCompIn H J) : IsQuasisimple ↥J :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.1

theorem isCompIn_map_conj_of_mem {H J : Subgroup G} (hJ : IsCompIn H J) {c : G} (hc : c ∈ H) :
    IsCompIn H (J.map (MulAut.conj c).toMonoidHom) := by
  have h := AS16.isCompIn_conj hJ c⁻¹
  have hH : conjugate H c⁻¹ = H := by
    have h1 : H.map (MulAut.conj c).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hc)
    simpa [conjugate] using h1
  rw [hH] at h
  simpa [conjugate] using h

theorem comps_le_two [Finite G] (hL : Lemma31Narrow) {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hH : H ≠ ⊤) (hz : z ∈ H)
    {K₁ K₂ K₃ : Subgroup ↥H} (h₁ : IsComponent K₁) (h₂ : IsComponent K₂) (h₃ : IsComponent K₃) :
    K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have hB : SecOfG G z ↥H (⟨z, hz⟩ : ↥H) :=
    ⟨H, ⊥, inferInstance, hz, hH, by simp, QuotientGroup.quotientBot, rfl⟩
  exact sec31_two hL hctx hB h₁ h₂ h₃ h12 h13 h23

theorem mem_normalizer_of_odd [Finite G] {H J : Subgroup G}
    (hc : ∀ K₁ K₂ K₃ : Subgroup ↥H, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃)
    (hJ : IsCompIn H J) {v : G} (hvH : v ∈ H) (hodd : Odd (orderOf v)) :
    v ∈ normalizer (J : Set G) := by
  have h := YCfg.mem_normalizer_of_odd_order (A := ↥H) hc hJ.2 (v := ⟨v, hvH⟩)
    (by rwa [Subgroup.orderOf_mk])
  rw [mem_normalizer_iff] at h ⊢
  intro x
  constructor
  · intro hx
    exact (h ⟨x, hJ.1 hx⟩).mp hx
  · intro hx
    have hvxH : v * x * v⁻¹ ∈ H := hJ.1 hx
    have hxH : x ∈ H := by
      have := H.mul_mem (H.mul_mem (H.inv_mem hvH) hvxH) hvH
      simpa [mul_assoc] using this
    exact (h ⟨x, hxH⟩).mpr hx

end Comps

section Swap

variable {G : Type} [Group G]

theorem mem_centralizer_of_comm_central {J : Subgroup G} [Group.IsPerfect ↥J] {g : G}
    (hg : g ∈ normalizer (J : Set G))
    (h : ∀ j ∈ J, ∀ k ∈ J, k * (g * j * g⁻¹ * j⁻¹) = (g * j * g⁻¹ * j⁻¹) * k) :
    g ∈ centralizer (J : Set G) := by
  have h1 : YCfg.yAct J ⟨g, hg⟩ = 1 := by
    ext x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center ↥J) x
    show (YCfg.yAct J ⟨g, hg⟩) (QuotientGroup.mk j) = QuotientGroup.mk j
    rw [YCfg.yAct_apply_mk]
    show QuotientGroup.mk _ = QuotientGroup.mk j
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have := h (j : G) j.2 (k : G) k.2
    simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  exact (YCfg.yAct_eq_one_iff J ⟨g, hg⟩).mp h1

theorem centralizes_of_swap [Finite G] {J P : Subgroup G} {z v : G} {p : ℕ} (hp : p.Prime)
    (hq : IsQuasisimple ↥J) (hz2 : z * z = 1)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a)
    (hP : IsPGroup p ↥P) (hMP : centralizer ({z} : Set G) ≤ normalizer (P : Set G))
    (hvP : v ∈ P) (hvJ : v ∈ normalizer (J : Set G)) (hvz : v * z = z * v) :
    v ∈ centralizer (J : Set G) := by
  have hperf : Group.IsPerfect ↥J := hq.1
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hJ' : ∀ x ∈ J, z * x * z⁻¹ ∈ J.map (MulAut.conj z).toMonoidHom := fun x hx =>
    ⟨x, hx, by simp [MulAut.conj_apply]⟩
  let δ : ↥J →* G :=
    { toFun := fun u => (u : G) * (z * (u : G) * z⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hc := hcomm (b : G) b.2 (z * (a : G) * z⁻¹) (hJ' _ a.2)
        calc ((a * b : ↥J) : G) * (z * ((a * b : ↥J) : G) * z⁻¹)
            = (a : G) * ((b : G) * (z * (a : G) * z⁻¹)) * (z * (b : G) * z⁻¹) := by
              simp only [Subgroup.coe_mul]; group
          _ = (a : G) * ((z * (a : G) * z⁻¹) * (b : G)) * (z * (b : G) * z⁻¹) := by rw [hc]
          _ = ((a : G) * (z * (a : G) * z⁻¹)) * ((b : G) * (z * (b : G) * z⁻¹)) := by group }
  have hδ : ∀ u : ↥J, δ u = (u : G) * (z * (u : G) * z⁻¹) := fun u => rfl
  have hδM : ∀ u : ↥J, δ u ∈ centralizer ({z} : Set G) := by
    intro u
    rw [Subgroup.mem_centralizer_singleton_iff, hδ]
    have hc := hcomm (u : G) u.2 (z * (u : G) * z⁻¹) (hJ' _ u.2)
    have hw : z * (z * (u : G) * z⁻¹) * z⁻¹ = (u : G) := by
      calc z * (z * (u : G) * z⁻¹) * z⁻¹ = (z * z) * (u : G) * (z * z)⁻¹ := by group
        _ = (u : G) := by rw [hz2]; group
    have h1 : z * ((u : G) * (z * (u : G) * z⁻¹)) * z⁻¹ = (u : G) * (z * (u : G) * z⁻¹) := by
      calc z * ((u : G) * (z * (u : G) * z⁻¹)) * z⁻¹
          = (z * (u : G) * z⁻¹) * (z * (z * (u : G) * z⁻¹) * z⁻¹) := by group
        _ = (z * (u : G) * z⁻¹) * (u : G) := by rw [hw]
        _ = (u : G) * (z * (u : G) * z⁻¹) := hc.symm
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hδP : ∀ n : ↥J, δ n ∈ P → ∀ g : ↥J, δ (g * n * g⁻¹) ∈ P := by
    intro n hn g
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hMP (hδM g)) (δ n)).mp hn
  have hN : (P.comap δ).Normal := ⟨fun n hn g => hδP n hn g⟩
  have hNle : P.comap δ ≤ center ↥J := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hle
    · exfalso
      have hall : ∀ u : ↥J, δ u ∈ P := fun u => by
        have : u ∈ P.comap δ := htop ▸ Subgroup.mem_top u
        exact this
      have hpg : IsPGroup p (↥J ⧸ center ↥J) := by
        intro y
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨a, ha⟩ := hP ⟨δ u, hall u⟩
        have hpow : (δ u) ^ (p ^ a) = 1 := congrArg Subtype.val ha
        have hcom : Commute (u : G) (z * (u : G) * z⁻¹) := hcomm (u : G) u.2 _ (hJ' _ u.2)
        have h1 : (u : G) ^ (p ^ a) * (z * (u : G) ^ (p ^ a) * z⁻¹) = 1 := by
          rw [hδ, hcom.mul_pow, conj_pow] at hpow
          exact hpow
        have hmem : ((u : G) ^ (p ^ a)) ∈ J.map (MulAut.conj z).toMonoidHom := by
          have h2 : (u : G) ^ (p ^ a) = (z * (u : G) ^ (p ^ a) * z⁻¹)⁻¹ :=
            eq_inv_of_mul_eq_one_left h1
          rw [h2]
          exact Subgroup.inv_mem _ (hJ' _ (J.pow_mem u.2 _))
        have hcenter : (u ^ (p ^ a) : ↥J) ∈ center ↥J := by
          rw [Subgroup.mem_center_iff]
          intro k
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_pow]
          exact hcomm (k : G) k.2 _ hmem
        have h3 : (QuotientGroup.mk u : ↥J ⧸ center ↥J) ^ (p ^ a) = 1 := by
          rw [← QuotientGroup.mk_pow]
          exact (QuotientGroup.eq_one_iff _).mpr hcenter
        exact ⟨a, h3⟩
      obtain ⟨-, hns⟩ := Gen.quasisimple_quot hq
      have : Fact p.Prime := ⟨hp⟩
      have := hpg.isNilpotent
      exact hns inferInstance
    · exact hle
  have := hperf
  refine mem_centralizer_of_comm_central hvJ fun j hj k hk => ?_
  have ha : v * j * v⁻¹ ∈ J := (mem_normalizer_iff.mp hvJ j).mp hj
  have hu : v * j * v⁻¹ * j⁻¹ ∈ J := J.mul_mem ha (J.inv_mem hj)
  have hzv : z * v = v * z := hvz.symm
  have e1 : z * (v * j * v⁻¹) * z⁻¹ = v * (z * j * z⁻¹) * v⁻¹ := by
    calc z * (v * j * v⁻¹) * z⁻¹ = (z * v) * j * (z * v)⁻¹ := by group
      _ = (v * z) * j * (v * z)⁻¹ := by rw [hzv]
      _ = v * (z * j * z⁻¹) * v⁻¹ := by group
  have hX : (v * (z * j * z⁻¹) * v⁻¹) * (z * j * z⁻¹)⁻¹ ∈ J.map (MulAut.conj z).toMonoidHom := by
    rw [← e1]
    exact Subgroup.mul_mem _ (hJ' _ ha) (Subgroup.inv_mem _ (hJ' _ hj))
  have hc := hcomm j⁻¹ (J.inv_mem hj) _ hX
  have hδu : δ ⟨v * j * v⁻¹ * j⁻¹, hu⟩ ∈ P := by
    have hdM := hMP (hδM ⟨j, hj⟩)
    have h1 : δ ⟨v * j * v⁻¹ * j⁻¹, hu⟩ =
        v * (δ ⟨j, hj⟩ * v⁻¹ * (δ ⟨j, hj⟩)⁻¹) := by
      rw [hδ, hδ]
      have e2 : z * (v * j * v⁻¹ * j⁻¹) * z⁻¹ =
          ((v * (z * j * z⁻¹) * v⁻¹) * (z * j * z⁻¹)⁻¹) := by
        calc z * (v * j * v⁻¹ * j⁻¹) * z⁻¹
            = (z * (v * j * v⁻¹) * z⁻¹) * (z * j * z⁻¹)⁻¹ := by group
          _ = _ := by rw [e1]
      show v * j * v⁻¹ * j⁻¹ * (z * (v * j * v⁻¹ * j⁻¹) * z⁻¹) = _
      rw [e2]
      calc v * j * v⁻¹ * j⁻¹ * ((v * (z * j * z⁻¹) * v⁻¹) * (z * j * z⁻¹)⁻¹)
          = (v * j * v⁻¹) * (j⁻¹ * ((v * (z * j * z⁻¹) * v⁻¹) * (z * j * z⁻¹)⁻¹)) := by group
        _ = (v * j * v⁻¹) * (((v * (z * j * z⁻¹) * v⁻¹) * (z * j * z⁻¹)⁻¹) * j⁻¹) := by rw [hc]
        _ = _ := by group
    rw [h1]
    exact P.mul_mem hvP ((mem_normalizer_iff.mp hdM v⁻¹).mp (P.inv_mem hvP))
  have hcen := hNle hδu
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨k, hk⟩)

end Swap

section Z

variable {G : Type} [Group G] [Finite G]

theorem z_mem_normalizer {z : G} {H J V P M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hz2 : orderOf z = 2) (hM : M = centralizer ({z} : Set G)) (hzH : z ∈ H)
    (hJ : IsCompIn H J) (hP : IsPGroup p ↥P) (hMP : M ≤ normalizer (P : Set G)) (hPM : P ≤ M)
    (hVP : V ≤ P) (hVN : V ≤ normalizer (J : Set G)) (hVc : ¬ V ≤ centralizer (J : Set G)) :
    z ∈ normalizer (J : Set G) := by
  by_contra hzn
  have hne : J ≠ J.map (MulAut.conj z).toMonoidHom := fun h =>
    hzn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hJ'c := isCompIn_map_conj_of_mem hJ hzH
  rcases AS16.isCompIn_commute hJ hJ'c with h | h
  · exact hne h
  · have hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a := by
      intro a ha b hb
      have h1 : ⁅a, b⁆ ∈ ⁅J, J.map (MulAut.conj z).toMonoidHom⁆ :=
        Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    have hz2' : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz2, pow_two] at this
    apply hVc
    intro v hv
    have hvz : v * z = z * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (hM ▸ hPM (hVP hv))
    exact centralizes_of_swap hp (quasisimple_of_isCompIn hJ) hz2' hcomm hP (hM ▸ hMP) (hVP hv)
      (hVN hv) hvz

omit [Finite G] in
theorem commutator_eq {z : G} {H J M : Subgroup G} (hM : M = centralizer ({z} : Set G))
    (hJ : IsCompIn H J) (hzN : z ∈ normalizer (J : Set G)) (hJM : ¬ J ≤ M) :
    ⁅J, zpowers z⁆ = J := by
  have hq : IsQuasisimple ↥J := quasisimple_of_isCompIn hJ
  have hperf : Group.IsPerfect ↥J := hq.1
  set L := ⁅J, zpowers z⁆ with hL
  have hLJ : L ≤ J := by
    rw [hL, Subgroup.commutator_le]
    intro a ha b hb
    have hbN : b ∈ normalizer (J : Set G) := (Subgroup.zpowers_le.mpr hzN) hb
    have h1 := (mem_normalizer_iff.mp hbN a⁻¹).mp (J.inv_mem ha)
    rw [commutatorElement_def]
    simpa [mul_assoc] using J.mul_mem ha h1
  have hnorm : ∀ g ∈ J, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg
    have h1 : L ≤ L.comap (MulAut.conj g).toMonoidHom := by
      rw [hL, Subgroup.commutator_le]
      intro a ha b hb
      show g * ⁅a, b⁆ * g⁻¹ ∈ L
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅g, b⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact L.mul_mem (Subgroup.commutator_mem_commutator (J.mul_mem hg ha) hb)
        (L.inv_mem (Subgroup.commutator_mem_commutator hg hb))
    intro l hl
    exact h1 hl
  have hLn : (L.subgroupOf J).Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ L := hn
    exact hnorm (g : G) g.2 (n : G) hn'⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hLn with htop | hcen
  · exact le_antisymm hLJ (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    apply hJM
    have := hperf
    have hzc : z ∈ centralizer (J : Set G) :=
      mem_centralizer_of_comm_central hzN fun j hj k hk => by
        have hmem : (⟨z * j * z⁻¹ * j⁻¹, by
            have h1 : z * j * z⁻¹ ∈ J := (mem_normalizer_iff.mp hzN j).mp hj
            exact J.mul_mem h1 (J.inv_mem hj)⟩ : ↥J) ∈ L.subgroupOf J := by
          have h1 : ⁅j, z⁆ ∈ L := Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers z)
          have h2 : ⁅z, j⁆ = ⁅j, z⁆⁻¹ := (commutatorElement_inv j z).symm
          show z * j * z⁻¹ * j⁻¹ ∈ L
          have h3 : z * j * z⁻¹ * j⁻¹ = ⁅z, j⁆ := by simp [commutatorElement_def]
          rw [h3, h2]
          exact L.inv_mem h1
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hmem) ⟨k, hk⟩)
    intro x hx
    rw [hM]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzc x hx)

end Z

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S3
