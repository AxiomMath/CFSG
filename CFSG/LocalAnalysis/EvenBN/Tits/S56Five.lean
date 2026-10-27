module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Basic
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Squeeze
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec5Two

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

@[expose] def s56Lg (d : Data G) : Set G := (d.zL ∩ d.A) \ {d.z}

@[expose] def s56Sg (d : Data G) : Set G := d.vL ∩ d.A

theorem s56_zL_le_L (d : Data G) : d.zL ⊆ d.L := by
  rintro _ ⟨l, hl, rfl⟩
  exact mul_mem (mul_mem hl d.z_mem) (inv_mem hl)

theorem s56_vL_le_L (d : Data G) : d.vL ⊆ d.L := by
  rintro _ ⟨l, hl, rfl⟩
  exact mul_mem (mul_mem hl d.v_mem) (inv_mem hl)

theorem s56_E_le_A (d : Data G) : d.E ≤ d.A := le_sup_left

theorem s56_t_mem_A (d : Data G) : d.t ∈ d.A := mem_sup_right (mem_zpowers _)

theorem Hyp.s56_z_mem_E (hd : d.Hyp) : d.z ∈ d.E := by
  have h := (hd.orbits_A).1
  have : d.z ∈ d.A ⊓ d.L := Subgroup.mem_inf.2 ⟨h.2, d.z_mem⟩
  rwa [hd.A_inf_L] at this

theorem Hyp.s56_zL_inter_A_le_E (hd : d.Hyp) {y : G} (hy : y ∈ d.zL ∩ d.A) : y ∈ d.E := by
  have : y ∈ d.A ⊓ d.L := Subgroup.mem_inf.2 ⟨hy.2, s56_zL_le_L d hy.1⟩
  rwa [hd.A_inf_L] at this

theorem Hyp.s56_vL_inter_A_le_E (hd : d.Hyp) {y : G} (hy : y ∈ d.vL ∩ d.A) : y ∈ d.E := by
  have : y ∈ d.A ⊓ d.L := Subgroup.mem_inf.2 ⟨hy.2, s56_vL_le_L d hy.1⟩
  rwa [hd.A_inf_L] at this

theorem Hyp.s56_z_ne_one (hd : d.Hyp) : d.z ≠ 1 := by
  intro h
  have hz := (hd.orbits_A).1.1
  rw [h] at hz
  exact (zL_vL_disjoint d).1 hz

theorem Hyp.s56_pv11_mul_z_mem (hd : d.Hyp) : d.pv 11 * d.z ∈ d.s56Lg := by
  have horb := (hd.orbits_A).2.2.1
  have h11 : d.pv 11 ∈ (d.zL ∩ d.A) \ {d.z} := by
    rw [← horb]
    exact ⟨1, one_mem _, by simp⟩
  have hF := Model.parrottF_long.2.1
  have h3 : titsZ * Model.parrottV 11 ∈ {f | f ∈ Model.parrottF ∧ Model.IsLong f} := by
    rw [hF]
    exact Or.inr (Or.inr rfl)
  have h2 : Model.parrottV 11 ∈ {f | f ∈ Model.parrottF ∧ Model.IsLong f} := by
    rw [hF]
    exact Or.inr (Or.inl rfl)
  have hD3 : titsZ * Model.parrottV 11 ∈ titsD := Model.parrottF_le_titsD h3.1
  have hD2 : Model.parrottV 11 ∈ titsD := Model.parrottF_le_titsD h2.1
  have hzL : d.z * d.pv 11 ∈ d.zL := by
    rw [zL_eq]
    refine ⟨titsZ * Model.parrottV 11, ⟨hD3, h3.2⟩, ?_⟩
    rw [d.lift_mul titsZ_mem_titsD hD2, lift_titsZ]
    rfl
  have hcomm : d.pv 11 * d.z = d.z * d.pv 11 := by
    have hzE := hd.s56_z_mem_E
    have hvE : d.pv 11 ∈ d.E := hd.s56_zL_inter_A_le_E ⟨h11.1.1, h11.1.2⟩
    exact congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm
      ⟨d.pv 11, s56_E_le_A d hvE⟩ ⟨d.z, s56_E_le_A d hzE⟩)
  rw [hcomm]
  refine ⟨⟨hzL, mul_mem (s56_E_le_A d hd.s56_z_mem_E) h11.1.2⟩, ?_⟩
  intro h
  rw [Set.mem_singleton_iff] at h
  have : d.pv 11 = 1 := by
    have h' : d.z * d.pv 11 = d.z * 1 := by rw [h, mul_one]
    exact mul_left_cancel h'
  exact (zL_vL_disjoint d).1 (this ▸ h11.1.1)

theorem s56_t_mem_M (d : Data G) : d.t ∈ d.M := d.s56_A_le_M d.s56_t_mem_A

theorem Hyp.s56_ME (hd : d.Hyp) : d.M ≤ normalizer (d.E : Set G) := by
  have := hd.M_le_normalizer
  rwa [hd.A_inf_L] at this

theorem Hyp.s56_M_comm_z (hd : d.Hyp) {m : G} (hm : m ∈ d.M) : m * d.z = d.z * m :=
  mem_centralizer_singleton_iff.1 (hd.M_le_centralizer_z hm)

theorem Hyp.s56_pv11_mem_Lg (hd : d.Hyp) : d.pv 11 ∈ d.s56Lg := by
  have horb := (hd.orbits_A).2.2.1
  have : d.pv 11 ∈ {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 11 * x⁻¹ = y} :=
    ⟨1, one_mem _, by simp⟩
  rw [horb] at this
  exact this

theorem Hyp.s56_pv10_mem_Sg (hd : d.Hyp) : d.pv 10 ∈ d.s56Sg := by
  have horb := (hd.orbits_A).2.2.2.2.1
  have : d.pv 10 ∈ {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 10 * x⁻¹ = y} :=
    ⟨1, one_mem _, by simp⟩
  rw [horb] at this
  exact this

theorem s56_mem_KOrb_iff {e₀ : G} (he₀ : e₀ ∈ d.M) {S : Set G}
    (horb : {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * e₀ * x⁻¹ = y} = S) (y : ↥d.M) :
    (y : G) ∈ S ↔
      y ∈ S56.KOrb (centralizer ({(⟨d.t, d.s56_t_mem_M⟩ : ↥d.M)} : Set ↥d.M)) ⟨e₀, he₀⟩ := by
  rw [← horb]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨⟨x, (Subgroup.mem_inf.1 hx).1⟩, ?_, Subtype.ext hxy⟩
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2)
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, Subgroup.mem_inf.2 ⟨k.2, ?_⟩, rfl⟩
    rw [mem_centralizer_singleton_iff] at hk ⊢
    exact congrArg Subtype.val hk

@[expose] noncomputable def s56SqueezeData (hd : d.Hyp) : S56.SqueezeData ↥d.M where
  E := d.E.subgroupOf d.M
  z := ⟨d.z, d.s56_E_le_M hd.s56_z_mem_E⟩
  t := ⟨d.t, d.s56_t_mem_M⟩
  Lg := {y | (y : G) ∈ d.s56Lg}
  Sg := {y | (y : G) ∈ d.s56Sg}
  normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have := (mem_normalizer_iff.1 (hd.s56_ME g.2) (a : G)).1 ha
    simpa using this⟩
  comm a ha b hb := by
    have ha' : (a : G) ∈ d.E := ha
    have hb' : (b : G) ∈ d.E := hb
    have hc := hd.A_facts.2.2.1.1.is_comm.comm ⟨(a : G), s56_E_le_A d ha'⟩ ⟨(b : G), s56_E_le_A d hb'⟩
    have hc' : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val hc
    exact Subtype.ext hc'
  sq a ha := by
    have ha' : (a : G) ∈ d.E := ha
    have := hd.A_facts.2.2.1.2 (a : G) (s56_E_le_A d ha')
    exact Subtype.ext (by simpa [pow_two] using this)
  card_E := by
    have hEM : d.E ≤ d.M := d.s56_E_le_M
    exact (Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv).trans hd.A_facts.1
  z_mem := Subgroup.mem_subgroupOf.2 hd.s56_z_mem_E
  z_ne := fun h => hd.s56_z_ne_one (congrArg Subtype.val h)
  z_central g := Subtype.ext (hd.s56_M_comm_z g.2)
  t_sq := Subtype.ext hd.t_mul_self
  t_conj m := by
    refine Subgroup.mem_subgroupOf.2 ?_
    have hs : d.t * d.t ∈ d.E := by rw [hd.t_mul_self]; exact one_mem _
    exact (hd.thm52 m.2 hs).1
  Lg_sub y hy := Subgroup.mem_subgroupOf.2 (hd.s56_zL_inter_A_le_E hy.1)
  Sg_sub y hy := Subgroup.mem_subgroupOf.2 (hd.s56_vL_inter_A_le_E hy)
  cover e he := by
    have he' : (e : G) ∈ d.E := he
    have hA : (e : G) ∈ d.A := s56_E_le_A d he'
    by_cases h1 : (e : G) = 1
    · exact Or.inl (Subtype.ext h1)
    · have hzv := mem_zL_or_vL d (X := Model.hatE)
        (fun x hx hx1 => Model.hatE_long_or_short hx hx1) (e := (e : G)) he' h1
      rcases hzv with hz | hv
      · by_cases h2 : (e : G) = d.z
        · exact Or.inr (Or.inl (Subtype.ext h2))
        · exact Or.inr (Or.inr (Or.inl ⟨⟨hz, hA⟩, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hv, hA⟩))
  disj := Set.disjoint_left.2 fun y hy hy' =>
    Set.disjoint_left.1 (zL_vL_disjoint d).2.2 hy.1.1 hy'.1
  one_nmem_Lg h := (zL_vL_disjoint d).1 h.1.1
  z_nmem_Lg h := h.2 (Set.mem_singleton _)
  one_nmem_Sg h := (zL_vL_disjoint d).2.1 h.1
  z_nmem_Sg h := Set.disjoint_left.1 (zL_vL_disjoint d).2.2 (hd.orbits_A).1.1 h.1
  Lg_orbit := ⟨⟨d.pv 11, d.s56_A_le_M (hd.s56_pv11_mem_Lg).1.2⟩,
    Set.ext (s56_mem_KOrb_iff _ (hd.orbits_A).2.2.1)⟩
  Sg_orbit := ⟨⟨d.pv 10, d.s56_A_le_M (hd.s56_pv10_mem_Sg).2⟩,
    Set.ext (s56_mem_KOrb_iff _ (hd.orbits_A).2.2.2.2.1)⟩
  Lg_card := by
    have hsub : d.s56Lg ⊆ Set.range (Subtype.val : ↥d.M → G) := fun y hy =>
      ⟨⟨y, d.s56_A_le_M hy.1.2⟩, rfl⟩
    rw [show {y : ↥d.M | (y : G) ∈ d.s56Lg} = Subtype.val ⁻¹' d.s56Lg from rfl,
      Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub]
    exact (hd.orbits_A).2.2.2.1
  Sg_card := by
    have hsub : d.s56Sg ⊆ Set.range (Subtype.val : ↥d.M → G) := fun y hy =>
      ⟨⟨y, d.s56_A_le_M hy.2⟩, rfl⟩
    rw [show {y : ↥d.M | (y : G) ∈ d.s56Sg} = Subtype.val ⁻¹' d.s56Sg from rfl,
      Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub]
    exact (hd.orbits_A).2.2.2.2.2
  Lg_z := by
    intro e he
    have horb := (hd.orbits_A).2.2.1
    have he' : (e : G) ∈ {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 11 * x⁻¹ = y} := by
      rw [horb]
      exact he
    obtain ⟨x, hx, hxe⟩ := he'
    have hpz : d.pv 11 * d.z ∈ {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G),
        x * d.pv 11 * x⁻¹ = y} := by
      rw [horb]
      exact hd.s56_pv11_mul_z_mem
    obtain ⟨x', hx', hx'e⟩ := hpz
    have hxz : x * d.z * x⁻¹ = d.z := by
      have := hd.s56_M_comm_z (Subgroup.mem_inf.1 hx).1
      calc x * d.z * x⁻¹ = (d.z * x) * x⁻¹ := by rw [this]
        _ = d.z := by group
    show (e : G) * d.z ∈ d.s56Lg
    rw [show d.s56Lg = {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 11 * x⁻¹ = y} from
      horb.symm]
    refine ⟨x * x', mul_mem hx hx', ?_⟩
    calc x * x' * d.pv 11 * (x * x')⁻¹ = x * (x' * d.pv 11 * x'⁻¹) * x⁻¹ := by group
      _ = x * (d.pv 11 * d.z) * x⁻¹ := by rw [hx'e]
      _ = (x * d.pv 11 * x⁻¹) * (x * d.z * x⁻¹) := by group
      _ = (e : G) * d.z := by rw [hxe, hxz]

theorem s56_E_le_L (d : Data G) : d.E ≤ d.L := d.liftSub_le _

theorem Hyp.s56_CA_eq (hd : d.Hyp) :
    S56.CA (s56SqueezeData hd).E (s56SqueezeData hd).t =
      (centralizer (d.A : Set G)).subgroupOf d.M := by
  have hc : ∀ p ∈ d.E, p * d.t = d.t * p := fun p hp => hd.L_comm_t (s56_E_le_L d hp)
  have hAM : ∀ a ∈ d.A, a ∈ d.M := fun a ha => d.s56_A_le_M ha
  ext m
  rw [Subgroup.mem_subgroupOf, S56.CA, Subgroup.mem_inf, mem_centralizer_iff, mem_centralizer_iff,
    mem_centralizer_iff]
  constructor
  · rintro ⟨hE, ht⟩ a ha
    have hmt : (m : G) * d.t = d.t * (m : G) := by
      have := ht (s56SqueezeData hd).t (Set.mem_singleton _)
      have h2 : (s56SqueezeData hd).t * m = m * (s56SqueezeData hd).t := this
      exact (congrArg Subtype.val h2).symm
    rcases (mem_sup_zpowers_iff hd.t_mul_self hc).1 ha with h | h
    · have h1 := hE ⟨a, hAM a ha⟩ (Subgroup.mem_subgroupOf.2 h)
      exact congrArg Subtype.val h1
    · have hte : d.t * a ∈ d.E := h
      have h1 := hE ⟨d.t * a, hAM _ (s56_E_le_A d hte)⟩ (Subgroup.mem_subgroupOf.2 hte)
      have h1' : (d.t * a) * (m : G) = (m : G) * (d.t * a) := congrArg Subtype.val h1
      have hta : a = d.t * (d.t * a) := by rw [← mul_assoc, hd.t_mul_self, one_mul]
      calc a * (m : G) = (d.t * (d.t * a)) * (m : G) := by rw [← hta]
        _ = d.t * ((d.t * a) * (m : G)) := by group
        _ = d.t * ((m : G) * (d.t * a)) := by rw [h1']
        _ = (d.t * (m : G)) * (d.t * a) := by group
        _ = ((m : G) * d.t) * (d.t * a) := by rw [hmt]
        _ = (m : G) * (d.t * (d.t * a)) := by group
        _ = (m : G) * a := by rw [← hta]
  · intro h
    refine ⟨fun e he => ?_, fun h' hh' => ?_⟩
    · have he' : (e : G) ∈ d.E := he
      exact Subtype.ext (h (e : G) (s56_E_le_A d he'))
    · rw [Set.mem_singleton_iff] at hh'
      rw [hh']
      exact Subtype.ext (h d.t d.s56_t_mem_A)

theorem s56_mem_zpowers_subtype_iff {M : Subgroup G} (z x : ↥M) :
    x ∈ zpowers z ↔ (x : G) ∈ zpowers (z : G) := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem Hyp.s56_centralizer_E_eq (hd : d.Hyp) :
    centralizer (((s56SqueezeData hd).E : Subgroup ↥d.M) : Set ↥d.M) =
      d.s56Q2.subgroupOf d.M := by
  ext m
  rw [Subgroup.mem_subgroupOf, s56Q2, Subgroup.mem_inf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨m.2, fun e he =>
      congrArg Subtype.val (h ⟨e, d.s56_E_le_M he⟩ (Subgroup.mem_subgroupOf.2 he))⟩
  · rintro ⟨-, h⟩ e he
    exact Subtype.ext (h (e : G) he)

theorem Hyp.s56_structure_M (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card d.M = 10240 * Nat.card (centralizer (d.A : Set G)) ∧
    Nat.card d.s56Q2 = 32 * Nat.card (centralizer (d.A : Set G)) ∧
    (∀ e ∈ d.E, ∃ m ∈ d.s56Q2, m * d.t * m⁻¹ = d.t * e) ∧
    (d.s56Q0 : Set G) = {m | m ∈ d.M ∧ ∀ e ∈ d.E, m * e * m⁻¹ * e⁻¹ ∈ zpowers d.z} ∧
    Nat.card d.s56Q0 = 512 * Nat.card (centralizer (d.A : Set G)) ∧
    Nat.card d.M = 20 * Nat.card d.s56Q0 ∧
    d.s56Q2 ≤ d.s56Q0 := by
  obtain ⟨h3, hcard⟩ := hd.s56_card_M_facts h49
  obtain ⟨hCp, -⟩ := hd.s56_centralizer_A
  have hcardCA : Nat.card (S56.CA (s56SqueezeData hd).E (s56SqueezeData hd).t) =
      Nat.card (centralizer (d.A : Set G)) := by
    rw [hd.s56_CA_eq]
    exact Nat.card_congr (subgroupOfEquivOfLe d.s56_centralizer_A_le_M).toEquiv
  have hC2 : IsPGroup 2 (S56.CA (s56SqueezeData hd).E (s56SqueezeData hd).t) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hCp
    exact IsPGroup.of_card (n := n) (by rw [hcardCA]; exact hn)
  obtain ⟨hN, hQ2, htrans, hK1, hidx, hcore⟩ :=
    S56.squeeze (s56SqueezeData hd) h3 (by rw [hcardCA]; exact hcard)
  rw [hcardCA] at hN hQ2 hK1
  have hQ0 : d.s56Q0 = (S56.K1 (s56SqueezeData hd).E (s56SqueezeData hd).z
      (s56SqueezeData hd).z_central).map d.M.subtype := by
    unfold s56Q0
    rw [hcore hC2]
  have hQ2le : d.s56Q2 ≤ d.M := inf_le_left
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd.s56_centralizer_E_eq] at hQ2
    rw [← hQ2]
    exact (Nat.card_congr (subgroupOfEquivOfLe hQ2le).toEquiv).symm
  · intro e he
    obtain ⟨m, hm, hme⟩ := htrans ⟨e, d.s56_E_le_M he⟩ (Subgroup.mem_subgroupOf.2 he)
    rw [hd.s56_centralizer_E_eq] at hm
    refine ⟨(m : G), Subgroup.mem_subgroupOf.1 hm, ?_⟩
    exact congrArg Subtype.val hme
  · rw [hQ0]
    ext m
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, fun e he => ?_⟩
      have h1 := hk ⟨e, d.s56_E_le_M he⟩ (Subgroup.mem_subgroupOf.2 he)
      exact (s56_mem_zpowers_subtype_iff _ _).1 h1
    · rintro ⟨hmM, h⟩
      refine ⟨⟨m, hmM⟩, ?_, rfl⟩
      intro e he
      exact (s56_mem_zpowers_subtype_iff _ _).2 (h (e : G) he)
  · rw [hQ0, Subgroup.card_map_of_injective d.M.subtype_injective]
    exact hK1
  · rw [hQ0, Subgroup.card_map_of_injective d.M.subtype_injective]
    have := Subgroup.card_mul_index
      (S56.K1 (s56SqueezeData hd).E (s56SqueezeData hd).z (s56SqueezeData hd).z_central)
    rw [hidx] at this
    rw [← this]
    ring
  · intro g hg
    rw [hQ0]
    have hgM : g ∈ d.M := hg.1
    have hgC : (⟨g, hgM⟩ : ↥d.M) ∈ centralizer (((s56SqueezeData hd).E : Subgroup ↥d.M) : Set ↥d.M) := by
      rw [hd.s56_centralizer_E_eq]
      exact Subgroup.mem_subgroupOf.2 hg
    exact ⟨⟨g, hgM⟩, S56.centralizer_le_K1 _ hgC, rfl⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
