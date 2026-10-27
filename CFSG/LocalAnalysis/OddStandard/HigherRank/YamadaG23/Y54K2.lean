module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54P
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Card

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private abbrev f4f0 (s : Setting3 G L) : G := s.fr.a₁ * s.fr.a₂

private lemma mul_comm_of_conj_eq {a b : G} (h : a * b * a⁻¹ = b) : a * b = b * a := by
  calc
    a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h]

private lemma isMulCommutative_cen (s : Setting3 G L) :
    IsMulCommutative ↥(cen s.fr.B) :=
  Subgroup.le_centralizer_iff_isMulCommutative.mp (by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2) w
      (Subgroup.mem_inf.mp hw).1)

private lemma f4f0_mem_F (s : Setting3 G L) : f4f0 s ∈ s.fr.F :=
  Subgroup.subset_closure (by simp [f4f0])

private lemma f4f0_mem_C2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : f4f0 c.s ∈ c.s.C₂ :=
  y54_B_le_C2 (s := c.s) (e := c.e) hH
    (y54_F_le_B (s := c.s) (e := c.e) hH (f4f0_mem_F c.s))

private noncomputable def f4rho (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ↥c.s.C₂ →* ↥(cen c.s.fr.B) :=
  MonoidHom.mk' (fun x => ⟨⁅(x : G), f4f0 c.s⁆,
      y54_C2_comm_V c hH (x : G) x.2 (f4f0 c.s) (f4f0_mem_C2 c hH)⟩)
    (fun a b => by
      haveI : IsMulCommutative ↥(cen c.s.fr.B) := isMulCommutative_cen c.s
      apply Subtype.ext
      change ⁅((a : G) * (b : G)), f4f0 c.s⁆ =
        ⁅(a : G), f4f0 c.s⁆ * ⁅(b : G), f4f0 c.s⁆
      have hbV : ⁅(b : G), f4f0 c.s⁆ ∈ cen c.s.fr.B :=
        y54_C2_comm_V c hH (b : G) b.2 (f4f0 c.s) (f4f0_mem_C2 c hH)
      have haV : ⁅(a : G), f4f0 c.s⁆ ∈ cen c.s.fr.B :=
        y54_C2_comm_V c hH (a : G) a.2 (f4f0 c.s) (f4f0_mem_C2 c hH)
      have hcent : (a : G) * ⁅(b : G), f4f0 c.s⁆ * (a : G)⁻¹ = ⁅(b : G), f4f0 c.s⁆ :=
        y54_C2_cent_V (s := c.s) (e := c.e) hH (a : G) a.2 _ hbV
      have hcomm : ⁅(b : G), f4f0 c.s⁆ * ⁅(a : G), f4f0 c.s⁆ =
          ⁅(a : G), f4f0 c.s⁆ * ⁅(b : G), f4f0 c.s⁆ :=
        congrArg Subtype.val (mul_comm' ⟨_, hbV⟩ ⟨_, haV⟩)
      rw [commutatorElement_mul_left_eq_conj_mul, hcent]
      exact hcomm)

private lemma f4rho_apply (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (x : ↥c.s.C₂) :
    (f4rho c hH x : G) = ⁅(x : G), f4f0 c.s⁆ := rfl

private lemma f4rho_eq_one (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (x : ↥c.s.C₂) :
    f4rho c hH x = 1 ↔ (x : G) ∈ Subgroup.centralizer (c.s.fr.F : Set G) := by
  constructor
  · intro hx
    have h1 : ⁅(x : G), f4f0 c.s⁆ = 1 := by
      have h2 : (f4rho c hH x : G) = 1 := by
        simpa using congrArg Subtype.val hx
      rwa [f4rho_apply] at h2
    have hxcomm : (x : G) * f4f0 c.s = f4f0 c.s * (x : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp h1
    have hcentV := y54_C2_cent_V (s := c.s) (e := c.e) hH (x : G) x.2
    have hcen : cen c.s.fr.B = closure {c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z} :=
      hH.hLF.fact14.2.2.1.1
    have hw0V : c.s.fr.b₁ * c.s.fr.b₂ ∈ cen c.s.fr.B := by
      rw [hcen]
      exact Subgroup.subset_closure (by simp)
    have hzV : c.s.fr.z ∈ cen c.s.fr.B := by
      rw [hcen]
      exact Subgroup.subset_closure (by simp)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [show (c.s.fr.F : Set G) = Subgroup.closure
      ({f4f0 c.s, c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z} : Set G) from rfl] at hy
    refine Subgroup.closure_induction (p := fun y _ => y * (x : G) = (x : G) * y)
      ?_ ?_ ?_ ?_ hy
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hxcomm.symm
      · exact (mul_comm_of_conj_eq (hcentV _ hw0V)).symm
      · exact (mul_comm_of_conj_eq (hcentV _ hzV)).symm
    · simp
    · intro y z hy hz ihy ihz
      calc
        (y * z) * (x : G) = y * (z * (x : G)) := by group
        _ = y * ((x : G) * z) := by rw [ihz]
        _ = (y * (x : G)) * z := by group
        _ = ((x : G) * y) * z := by rw [ihy]
        _ = (x : G) * (y * z) := by group
    · intro y hy ihy
      calc
        y⁻¹ * (x : G) = y⁻¹ * ((x : G) * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * (x : G)) * y⁻¹ := by rw [← ihy]
        _ = (x : G) * y⁻¹ := by group
  · intro hx
    have hf0 : f4f0 c.s ∈ c.s.fr.F := f4f0_mem_F c.s
    apply Subtype.ext
    simp only [f4rho_apply, Subgroup.coe_one]
    exact Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hx (f4f0 c.s) hf0

private noncomputable def f4rhoB (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ↥c.s.fr.B →* ↥(cen c.s.fr.B) :=
  (f4rho c hH).comp (Subgroup.inclusion (y54_B_le_C2 (s := c.s) (e := c.e) hH))

private lemma f4rhoB_ker (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    (f4rhoB c hH).ker = c.s.fr.F.subgroupOf c.s.fr.B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hb' : f4rho c hH (Subgroup.inclusion
        (y54_B_le_C2 (s := c.s) (e := c.e) hH) b) = f4rhoB c hH b := rfl
  rw [← hb', f4rho_eq_one c hH]
  rw [Subgroup.coe_inclusion]
  constructor
  · intro hx
    have hbL : (b : G) ∈ L := f3_B_le_L c.s b.2
    have hbcent : (b : G) ∈ Subgroup.centralizer (c.s.fr.F : Set G) := hx
    have hbLF : (b : G) ∈ centIn L c.s.fr.F := Subgroup.mem_inf.mpr ⟨hbL, hbcent⟩
    rwa [y54_centIn_L_F (s := c.s) (e := c.e) hH] at hbLF
  · intro hbF
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact y54_F_comm (s := c.s) (e := c.e) hH y hy (b : G) hbF

theorem y54_F_le_K {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.F ≤ centIn (M2 s) s.fr.F := by
  intro f hf
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact y54_B_le_M2 s (y54_F_le_B (s := s) (e := e) hH hf)
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact y54_F_comm (s := s) (e := e) hH g hg f hf

theorem y54_K_inf_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    centIn (M2 s) s.fr.F ⊓ s.fr.B = s.fr.F := by
  refine le_antisymm ?_ ?_
  · intro k hk
    obtain ⟨hkK, hkB⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨_, hkcent⟩ := Subgroup.mem_inf.mp hkK
    have hkL : k ∈ L := f3_B_le_L s hkB
    have hkmem : k ∈ centIn L s.fr.F := Subgroup.mem_inf.mpr ⟨hkL, hkcent⟩
    rwa [y54_centIn_L_F (s := s) (e := e) hH] at hkmem
  · intro f hf
    exact Subgroup.mem_inf.mpr ⟨y54_F_le_K (s := s) (e := e) hH hf,
      y54_F_le_B (s := s) (e := e) hH hf⟩

theorem y54_K_norm_B (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ k ∈ centIn (M2 c.s) c.s.fr.F, ∀ b ∈ c.s.fr.B, k * b * k⁻¹ ∈ c.s.fr.B := by
  intro k hk b hb
  exact y54_C2_norm_B (s := c.s) (e := c.e) hH k
    (y54_M2_le_C2 c hH (Subgroup.mem_inf.mp hk).1) b hb

theorem y54_B_cover (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ m ∈ M2 c.s, ∃ b ∈ c.s.fr.B, b⁻¹ * m ∈ centIn (M2 c.s) c.s.fr.F := by
  have hBC2 : c.s.fr.B ≤ c.s.C₂ := y54_B_le_C2 (s := c.s) (e := c.e) hH
  have hcardF : Nat.card ↥(c.s.fr.F) = 8 := by
    have h := (y54_F_isE3 (s := c.s) (e := c.e) hH).2
    norm_num at h
    exact h
  have hindex : (c.s.fr.F.subgroupOf c.s.fr.B).index = 4 := by
    show c.s.fr.F.relIndex c.s.fr.B = 4
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := c.s.fr.B)
    rw [inf_eq_left.mpr (y54_F_le_B (s := c.s) (e := c.e) hH), hcardF,
      y54_card_B (s := c.s) (e := c.e) hH] at h
    omega
  have hcard_range : Nat.card ↥(f4rhoB c hH).range = 4 := by
    have h := Subgroup.index_ker (f4rhoB c hH)
    rw [f4rhoB_ker c hH, hindex] at h
    exact h.symm
  have htop : (f4rhoB c hH).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard_range]
    have h := (f3_V_isE2 (s := c.s) (e := c.e) hH).2
    norm_num at h
    exact h.symm
  intro m hm
  have hmC2 : m ∈ c.s.C₂ := y54_M2_le_C2 c hH hm
  have hmrange : f4rho c hH ⟨m, hmC2⟩ ∈ (f4rhoB c hH).range := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hmrange
  have hb' : f4rho c hH (Subgroup.inclusion hBC2 b) = f4rho c hH ⟨m, hmC2⟩ := hb
  have hx1 : f4rho c hH ((Subgroup.inclusion hBC2 b)⁻¹ * (⟨m, hmC2⟩ : ↥c.s.C₂)) = 1 := by
    simp only [map_mul, map_inv, hb', inv_mul_cancel]
  have hxcent : (((Subgroup.inclusion hBC2 b)⁻¹ * (⟨m, hmC2⟩ : ↥c.s.C₂) : ↥c.s.C₂) : G) ∈
      Subgroup.centralizer (c.s.fr.F : Set G) := (f4rho_eq_one c hH _).mp hx1
  refine ⟨(b : G), b.2, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
  · exact (M2 c.s).mul_mem ((M2 c.s).inv_mem (y54_B_le_M2 c.s b.2)) hm
  · simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using hxcent

theorem y54_M2_eq_KB (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    M2 c.s = centIn (M2 c.s) c.s.fr.F ⊔ c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · intro m hm
    obtain ⟨b, hb, hbm⟩ := y54_B_cover c hH m hm
    have hm_eq : m = b * (b⁻¹ * m) := by group
    rw [hm_eq]
    have hsup := Subgroup.mul_mem_sup (S := c.s.fr.B) (T := centIn (M2 c.s) c.s.fr.F) hb hbm
    rwa [sup_comm] at hsup
  · exact sup_le inf_le_left (y54_B_le_M2 c.s)

theorem y54_K_le_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    centIn (M2 c.s) c.s.fr.F ≤ f4Y c.s := by
  intro k hk
  obtain ⟨hkM2, hkcent⟩ := Subgroup.mem_inf.mp hk
  refine Subgroup.mem_inf.mpr ⟨?_, hkcent⟩
  exact y54_C2_le_X c hH (y54_M2_le_C2 c hH hkM2)

end CFSG.OddStandard.HigherRank.YamadaG23
