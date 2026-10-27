module

public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow

public section

namespace CFSG.QuasithinUnique.Setup

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

section Rho

variable {V P : Subgroup G}

theorem coe_conjAct_apply (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

@[expose] noncomputable def rho (V P : Subgroup G) (hP : P ≤ Subgroup.normalizer (V : Set G)) :
    P →* MulAut V :=
  (conjAct V).comp (Subgroup.inclusion hP)

theorem rho_apply_coe (hP : P ≤ Subgroup.normalizer (V : Set G)) (p : P) (v : V) :
    ((rho V P hP p v : V) : G) = p * v * (p : G)⁻¹ :=
  coe_conjAct_apply (Subgroup.inclusion hP p) v

theorem range_rho (hP : P ≤ Subgroup.normalizer (V : Set G)) :
    (rho V P hP).range = autOn P V := by
  unfold rho autOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem rho_eq_one_iff (hP : P ≤ Subgroup.normalizer (V : Set G)) (p : P) :
    rho V P hP p = 1 ↔ (p : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h
    simp only [rho_apply_coe, MulAut.one_apply] at this
    have h2 : (p : G) * v * (p : G)⁻¹ = v := this
    calc v * (p : G) = ((p : G) * v * (p : G)⁻¹) * p := by rw [h2]
      _ = p * v := by group
  · intro hc
    ext v
    rw [rho_apply_coe, MulAut.one_apply]
    have h := Subgroup.mem_centralizer_iff.mp hc v v.2
    show (p : G) * v * (p : G)⁻¹ = v
    rw [← h, mul_inv_cancel_right]

theorem mem_autOn_iff {X : Subgroup G} {φ : MulAut V} :
    φ ∈ autOn X V ↔ ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ X ∧ conjAct V g = φ :=
  CFSG.Quasithin.AutOn.mem_autOn_iff

theorem mem_autOn_iff_rho (hP : P ≤ Subgroup.normalizer (V : Set G)) {X : Subgroup G}
    (hXP : X ≤ P) {φ : MulAut V} :
    φ ∈ autOn X V ↔ ∃ p : P, (p : G) ∈ X ∧ rho V P hP p = φ := by
  rw [mem_autOn_iff]
  constructor
  · rintro ⟨g, hgX, rfl⟩
    exact ⟨⟨g, hXP hgX⟩, hgX, rfl⟩
  · rintro ⟨p, hpX, rfl⟩
    exact ⟨Subgroup.inclusion hP p, hpX, rfl⟩

theorem mem_autOn_self_iff (hP : P ≤ Subgroup.normalizer (V : Set G)) {φ : MulAut V} :
    φ ∈ autOn P V ↔ ∃ p : P, rho V P hP p = φ := by
  rw [← range_rho hP]
  exact MonoidHom.mem_range

@[expose] noncomputable def rhoPreimage (V P : Subgroup G)
    (hP : P ≤ Subgroup.normalizer (V : Set G)) (N : Subgroup (MulAut V)) : Subgroup G where
  carrier := {g | ∃ h : g ∈ P, rho V P hP ⟨g, h⟩ ∈ N}
  one_mem' := ⟨P.one_mem, by
    have : rho V P hP ⟨1, P.one_mem⟩ = 1 := map_one _
    rw [this]
    exact N.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hna⟩ ⟨hb, hnb⟩
    refine ⟨P.mul_mem ha hb, ?_⟩
    have : rho V P hP ⟨a * b, P.mul_mem ha hb⟩ = rho V P hP ⟨a, ha⟩ * rho V P hP ⟨b, hb⟩ :=
      map_mul _ (⟨a, ha⟩ : P) ⟨b, hb⟩
    rw [this]
    exact N.mul_mem hna hnb
  inv_mem' := by
    rintro a ⟨ha, hna⟩
    refine ⟨P.inv_mem ha, ?_⟩
    have : rho V P hP ⟨a⁻¹, P.inv_mem ha⟩ = (rho V P hP ⟨a, ha⟩)⁻¹ :=
      map_inv _ (⟨a, ha⟩ : P)
    rw [this]
    exact N.inv_mem hna

theorem mem_rhoPreimage {hP : P ≤ Subgroup.normalizer (V : Set G)} {N : Subgroup (MulAut V)}
    {p : P} : (p : G) ∈ rhoPreimage V P hP N ↔ rho V P hP p ∈ N :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨p.2, h⟩⟩

theorem rhoPreimage_le (hP : P ≤ Subgroup.normalizer (V : Set G)) (N : Subgroup (MulAut V)) :
    rhoPreimage V P hP N ≤ P := fun _ hg => hg.1

theorem le_normalizer_rhoPreimage (hP : P ≤ Subgroup.normalizer (V : Set G))
    {N : Subgroup (MulAut V)} (hN : autOn P V ≤ Subgroup.normalizer (N : Set (MulAut V))) :
    P ≤ Subgroup.normalizer (rhoPreimage V P hP N : Set G) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rintro _ ⟨x, ⟨hx, hxN⟩, rfl⟩
  have hgx : g * x * g⁻¹ ∈ P := P.mul_mem (P.mul_mem hg hx) (P.inv_mem hg)
  refine ⟨hgx, ?_⟩
  have hρ : rho V P hP ⟨(MulAut.conj g).toMonoidHom x, hgx⟩ =
      rho V P hP ⟨g, hg⟩ * rho V P hP ⟨x, hx⟩ * (rho V P hP ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  rw [hρ]
  have hgΛ : rho V P hP ⟨g, hg⟩ ∈ autOn P V := (mem_autOn_self_iff hP).mpr ⟨⟨g, hg⟩, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hN hgΛ) _).mp hxN

end Rho

section Image

variable [Finite G] {V P S : Subgroup G}

theorem isSylowTwoOf_autOn (hSP : IsSylowTwoOf S P) (hP : P ≤ Subgroup.normalizer (V : Set G)) :
    IsSylowTwoOf (autOn S V) (autOn P V) :=
  CFSG.Quasithin.AutOn.isSylowTwoOf_autOn hSP hP

omit [Finite G] in
theorem pCoreOf_autOn_eq_bot (hV : IsTwoReducedIn P V) :
    pCoreOf 2 (autOn P V) = ⊥ := by
  have hP : P ≤ Subgroup.normalizer (V : Set G) := hV.2.1
  set N : Subgroup (MulAut V) := pCoreOf 2 (autOn P V) with hN
  have hNΛ : N ≤ autOn P V := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
  have hΛN : autOn P V ≤ Subgroup.normalizer (N : Set (MulAut V)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  have hN2 : IsPGroup 2 N := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hDred := hV.2.2.2 (rhoPreimage V P hP N) (rhoPreimage_le hP N)
    (le_normalizer_rhoPreimage hP hΛN) (fun d hd => by
      obtain ⟨hdP, hdN⟩ := hd
      obtain ⟨k, hk⟩ := hN2 ⟨rho V P hP ⟨d, hdP⟩, hdN⟩
      refine ⟨k, ?_⟩
      have h1 : rho V P hP ⟨d, hdP⟩ ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      rw [← map_pow] at h1
      exact (rho_eq_one_iff hP _).mp h1)
  refine eq_bot_iff.mpr fun n hn => ?_
  obtain ⟨p, hp⟩ := (mem_autOn_self_iff hP).mp (hNΛ hn)
  have hpD : (p : G) ∈ rhoPreimage V P hP N := mem_rhoPreimage.mpr (hp ▸ hn)
  have := (rho_eq_one_iff hP p).mpr (hDred hpD)
  rw [Subgroup.mem_bot, ← hp]
  exact this

theorem not_normal_autOn (hSP : IsSylowTwoOf S P) (hP : P ≤ Subgroup.normalizer (V : Set G))
    (hΛ : pCoreOf 2 (autOn P V) = ⊥) (hCS : S ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 P)
    (hnn : ¬ P ≤ Subgroup.normalizer (S : Set G)) :
    ¬ ((autOn S V).subgroupOf (autOn P V)).Normal := by
  intro hnormal
  have hsyl := isSylowTwoOf_autOn hSP hP
  have hle : autOn S V ≤ pCoreOf 2 (autOn P V) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hsyl.le hnormal
      hsyl.isPGroup
  rw [hΛ] at hle
  have hSC : S ≤ Subgroup.centralizer (V : Set G) := by
    by_contra h
    exact autOn_ne_bot_of_not_le_centralizer (hSP.le.trans hP) h (le_bot_iff.mp hle)
  have hS : S = pCoreOf 2 P := by rw [← hCS]; exact (inf_of_le_left hSC).symm
  exact hnn (hS ▸ CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 P)

omit [Finite G] in
theorem autOn_max (hP : P ≤ Subgroup.normalizer (V : Set G)) {I : Subgroup G} (hSI : S ≤ I)
    (hIP : I < P) (hmax : ∀ X : Subgroup G, S ≤ X → X < P → X ≤ I)
    (hC : P ⊓ Subgroup.centralizer (V : Set G) ≤ I) (hSP : S ≤ P) :
    autOn S V ≤ autOn I V ∧ autOn I V < autOn P V ∧
      ∀ X : Subgroup (MulAut V), autOn S V ≤ X → X < autOn P V → X ≤ autOn I V := by
  refine ⟨autOn_le_autOn V hSI, lt_of_le_of_ne (autOn_le_autOn V hIP.le) fun heq => ?_, ?_⟩
  ·
    refine absurd (fun p (hp : p ∈ P) => ?_ : P ≤ I) (not_le_of_gt hIP)
    have hpΛ : rho V P hP ⟨p, hp⟩ ∈ autOn I V := by
      rw [heq]
      exact (mem_autOn_self_iff hP).mpr ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨q, hqI, hq⟩ := (mem_autOn_iff_rho hP hIP.le).mp hpΛ
    have h1 : rho V P hP (q⁻¹ * ⟨p, hp⟩) = 1 := by rw [map_mul, map_inv, hq, inv_mul_cancel]
    have h2 : ((q⁻¹ * ⟨p, hp⟩ : P) : G) ∈ P ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨(q⁻¹ * ⟨p, hp⟩ : P).2, (rho_eq_one_iff hP _).mp h1⟩
    have h3 := hC h2
    have : p = (q : G) * ((q⁻¹ * ⟨p, hp⟩ : P) : G) := by simp
    rw [this]
    exact I.mul_mem hqI h3
  · intro X hSX hXΛ x hx
    set Y : Subgroup G := rhoPreimage V P hP X with hY
    have hSY : S ≤ Y := fun s hs => by
      refine mem_rhoPreimage (p := ⟨s, hSP hs⟩) |>.mpr (hSX ?_)
      exact (mem_autOn_iff_rho hP hSP).mpr ⟨⟨s, hSP hs⟩, hs, rfl⟩
    have hYP : Y < P := by
      refine lt_of_le_of_ne (rhoPreimage_le hP X) fun heq => ?_
      refine absurd (fun φ hφ => ?_ : autOn P V ≤ X) (not_le_of_gt hXΛ)
      obtain ⟨p, rfl⟩ := (mem_autOn_self_iff hP).mp hφ
      have hpY : (p : G) ∈ Y := by
        rw [heq]
        exact p.2
      exact mem_rhoPreimage.mp hpY
    have hYI : Y ≤ I := hmax Y hSY hYP
    obtain ⟨p, rfl⟩ := (mem_autOn_self_iff hP).mp (hXΛ.le hx)
    exact (mem_autOn_iff_rho hP hIP.le).mpr ⟨p, hYI (mem_rhoPreimage.mpr hx), rfl⟩

theorem autOn_oddOrderSubgroup (hP : P ≤ Subgroup.normalizer (V : Set G)) :
    autOn (oddOrderSubgroup P) V = oddOrderSubgroup (autOn P V) := by
  have hK : oddOrderSubgroup P ≤ P := oddOrderSubgroup_le P
  apply le_antisymm
  · intro φ hφ
    obtain ⟨p, hpK, rfl⟩ := (mem_autOn_iff_rho hP hK).mp hφ
    have hle : oddOrderSubgroup P ≤ rhoPreimage V P hP (oddOrderSubgroup (autOn P V)) := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      rw [SetLike.mem_coe]
      refine (mem_rhoPreimage (p := ⟨x, hx.1⟩)).mpr (Subgroup.subset_closure ⟨?_, ?_⟩)
      · exact (mem_autOn_self_iff hP).mpr ⟨⟨x, hx.1⟩, rfl⟩
      · have := orderOf_map_dvd (rho V P hP) (⟨x, hx.1⟩ : P)
        rw [Subgroup.orderOf_mk] at this
        exact Odd.of_dvd_nat hx.2 this
    exact mem_rhoPreimage.mp (hle hpK)
  · refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨p, rfl⟩ := (mem_autOn_self_iff hP).mp hy.1
    obtain ⟨k, hk⟩ := exists_pow_mem_oddOrderSubgroup (H := P) p.2
    have hmem : rho V P hP p ^ (2 ^ k) ∈ autOn (oddOrderSubgroup P) V := by
      rw [← map_pow]
      exact (mem_autOn_iff_rho hP hK).mpr ⟨p ^ (2 ^ k), hk, rfl⟩
    exact mem_of_odd_orderOf_of_pow_mem hy.2 hmem

end Image

theorem ReducedAction.isKGroupCat_autOn {G : Type} [Group G] {S P V : Subgroup G}
    (hR : ReducedAction G S P V) : CFSG.SectionRank.IsKGroupCat (autOn P V) := by
  have hP := hR.le_normalizer
  have h1 : CFSG.SectionRank.IsKGroupCat (↥P ⧸ (rho V P hP).ker) :=
    CFSG.SectionRank.IsKGroupCat.quotient hR.obstruction.sqtk.2 _
  have h2 : CFSG.SectionRank.IsKGroupCat ↥(rho V P hP).range :=
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv h1
      (QuotientGroup.quotientKerEquivRange (rho V P hP)).symm
  exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv h2 (MulEquiv.subgroupCongr (range_rho hP).symm)

end CFSG.QuasithinUnique.Setup
