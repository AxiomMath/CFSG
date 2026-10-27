module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneSyl
import CFSG.CGT.PushingUpLit.CGT6.EmbAltK3

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

theorem cbo_perfect_le_of_index_two {Γ : Type*} [Group Γ] {X₀ P : Subgroup Γ}
    (hX₀ : X₀.index = 2) (hP : ⁅P, P⁆ = P) : P ≤ X₀ := by
  have hcomm : ∀ g h : Γ, g * h * g⁻¹ * h⁻¹ ∈ X₀ := by
    intro g h
    have e1 := Subgroup.mul_mem_iff_of_index_two hX₀ (a := g * h) (b := g⁻¹ * h⁻¹)
    have e2 := Subgroup.mul_mem_iff_of_index_two hX₀ (a := g) (b := h)
    have e3 := Subgroup.mul_mem_iff_of_index_two hX₀ (a := g⁻¹) (b := h⁻¹)
    have e4 : g⁻¹ ∈ X₀ ↔ g ∈ X₀ := ⟨fun h' => by simpa using X₀.inv_mem h', X₀.inv_mem_iff.mpr⟩
    have e5 : h⁻¹ ∈ X₀ ↔ h ∈ X₀ := ⟨fun h' => by simpa using X₀.inv_mem h', X₀.inv_mem_iff.mpr⟩
    have : g * h * (g⁻¹ * h⁻¹) ∈ X₀ := by
      rw [e1, e2, e3, e4, e5]
    simpa [mul_assoc] using this
  have h1 : ⁅P, P⁆ ≤ X₀ := by
    rw [Subgroup.commutator_le]
    intro g _ h _
    exact hcomm g h
  rwa [hP] at h1

theorem cbo_perfect_le_of_sup_pgroup {Γ : Type*} [Group Γ] [Finite Γ] {L T P : Subgroup Γ}
    (hL : L.Normal) (hT : IsPGroup 2 ↥T) (hLT : L ⊔ T = ⊤) (hP : ⁅P, P⁆ = P) : P ≤ L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmk : Function.Surjective ((QuotientGroup.mk' L).comp T.subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ T ⊔ L := by rw [sup_comm, hLT]; trivial
    have hgp : g ∈ (↑(T ⊔ L) : Set Γ) := hg
    rw [Subgroup.mul_normal T L] at hgp
    obtain ⟨τ, hτ, l, hl, rfl⟩ := hgp
    refine ⟨⟨τ, hτ⟩, ?_⟩
    show (QuotientGroup.mk' L) τ = QuotientGroup.mk' L (τ * l)
    have h1 : QuotientGroup.mk' L l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [map_mul, h1, mul_one]
  have hQ : IsPGroup 2 (Γ ⧸ L) := hT.of_surjective _ hmk
  have hnil : Group.IsNilpotent (Γ ⧸ L) := hQ.isNilpotent
  have hsol : Group.IsSolvable (Γ ⧸ L) := inferInstance
  let f : ↥P →* Γ ⧸ L := (QuotientGroup.mk' L).comp P.subtype
  have hperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hr : Group.IsPerfect ↥f.range := hperf.range f
  have hsub : Subsingleton ↥f.range := by
    by_contra hn
    have : Nontrivial ↥f.range := not_subsingleton_iff_nontrivial.mp hn
    exact Group.IsPerfect.not_isSolvable (G := ↥f.range) inferInstance
  intro x hx
  have h1 : f ⟨x, hx⟩ = 1 := by
    have := Subsingleton.elim (⟨f ⟨x, hx⟩, ⟨_, rfl⟩⟩ : ↥f.range) 1
    exact congrArg Subtype.val this
  exact (QuotientGroup.eq_one_iff x).mp h1

variable {V : Type} [CommGroup V] [Finite V] {Y X G T : Subgroup (MulAut V)} {t : MulAut V}
  {m : ℕ}

omit [Finite V] in
theorem cbo_commutator_subgroupOf_self {N P : Subgroup (MulAut V)} (hPN : P ≤ N)
    (hperf : ⁅P, P⁆ = P) : ⁅P.subgroupOf N, P.subgroupOf N⁆ = P.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN, hperf]

omit [Finite V] in
theorem cbo_conjClosure_normal (G Y : Subgroup (MulAut V)) :
    ((conjClosure Y G).subgroupOf G).Normal :=
  ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure g.2) n).mp hn⟩

namespace OneCfg

variable (c : OneCfg G T Y t m X)

include c in
theorem L_le_G : conjClosure Y G ≤ G := conjClosure_le c.Y_le_G

include c in
theorem L_perfect : ⁅conjClosure Y G, conjClosure Y G⁆ = conjClosure Y G :=
  commutator_conjClosure_eq_self c.cfg.adm.hperf

include c in
theorem L_center_eq_bot : Subgroup.center ↥(conjClosure Y G) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine c.cfg.eq_one_of_commute c.hV c.hm c.hodd c.hY fun l hl => ?_
  have := Subgroup.mem_center_iff.mp hz ⟨l, hl⟩
  exact congrArg Subtype.val this.symm

include c in
theorem perfect_le_L {P : Subgroup (MulAut V)} (hPG : P ≤ G) (hP : ⁅P, P⁆ = P) :
    P ≤ conjClosure Y G := by
  classical
  have hLn := cbo_conjClosure_normal G Y
  have hTG : T ≤ G := c.cfg.adm.hTG
  have hT2 : IsPGroup 2 ↥(T.subgroupOf G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 c.cfg.adm.hT2
    exact (IsPGroup.iff_card).2 ⟨n, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv]; exact hn⟩
  have hLT : (conjClosure Y G).subgroupOf G ⊔ T.subgroupOf G = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr c.L_le_G, inf_eq_left.mpr hTG, c.cfg.gen, Subgroup.map_top,
      Subgroup.range_subtype]
  have hPp := cbo_commutator_subgroupOf_self hPG hP
  have := cbo_perfect_le_of_sup_pgroup hLn hT2 hLT hPp
  intro x hx
  exact this (show (⟨x, hPG hx⟩ : ↥G) ∈ P.subgroupOf G from hx)

include c in
theorem L_lt_G : conjClosure Y G < G := by
  obtain ⟨X₀, hX₀n, hX₀i, htX₀⟩ := c.exists_index_two
  refine lt_of_le_of_ne c.L_le_G fun hLG => ?_
  have hperf := cbo_commutator_subgroupOf_self c.L_le_G c.L_perfect
  have hle := cbo_perfect_le_of_index_two hX₀i hperf
  have htop : (conjClosure Y G).subgroupOf G = ⊤ := by rw [hLG]; exact Subgroup.subgroupOf_self G
  rw [htop] at hle
  exact htX₀ (hle (Subgroup.mem_top _))

include c in
theorem L_simple : IsSimpleGroup ↥(conjClosure Y G) := by
  have hq : IsSimpleGroup (↥(conjClosure Y G) ⧸ Subgroup.center ↥(conjClosure Y G)) :=
    c.cfg.quasi.2
  have hcen := c.L_center_eq_bot
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥(conjClosure Y G))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen]
  exact (MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩).isSimpleGroup

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
