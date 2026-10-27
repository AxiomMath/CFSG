module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Cl2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E614Def
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Ker2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c

variable {c}

theorem IsRs.exists_conj_of_not_mem_R {Rs : Subgroup G} (hR : c.IsRs Rs)
    {y : G} (hy : y ∈ Rs) (hyR : y ∉ Rs ⊓ c.N1) (hy2 : y * y = 1)
    (ha : ∀ r : G, ∀ hr : r ∈ Rs ⊓ c.N1, y * z = r →
      ((c.rho ⟨r, hr.2⟩).1, (1 : MulAut ↥E)) ∈ c.Rhat (Rs ⊓ c.N1)) :
    ∃ u ∈ Rs ⊓ c.N1, y = u * z * u⁻¹ := by
  have hzz : z * z = 1 := c.h.z_sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hidx : ((Rs ⊓ c.N1).subgroupOf Rs).index = 2 := hR.relIndex_R.1
  have hzR : z ∉ Rs ⊓ c.N1 := hR.relIndex_R.2
  have hr : y * z ∈ Rs ⊓ c.N1 := by
    have h2 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hy⟩ : ↥Rs))
      (b := (⟨z, hR.z_mem⟩ : ↥Rs))).2 ⟨fun h => absurd h hyR, fun h => absurd h hzR⟩
    exact h2
  obtain ⟨r, hrdef⟩ : ∃ r : G, r = y * z := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hrN : r ∈ c.N1 := hr.2
  have hzr : z * r * z⁻¹ = r⁻¹ := by
    have e1 : z * r * z⁻¹ = z * y := by
      rw [hrdef, hzi]
      calc z * (y * z) * z = z * y * (z * z) := by group
        _ = z * y := by rw [hzz, mul_one]
    have e2 : r⁻¹ = z * y := by rw [hrdef, mul_inv_rev, hzi, hyi]
    exact e1.trans e2.symm
  have hzr' : z * r = r⁻¹ * z := by
    calc z * r = (z * r * z⁻¹) * z := by group
      _ = r⁻¹ * z := by rw [hzr]
  let n : ↥c.N1 := ⟨r, hrN⟩
  have hzn : c.zconjN1 n = n⁻¹ := Subtype.ext (by
    show z * r * z⁻¹ = r⁻¹
    exact hzr)
  have hρn : c.rho (c.zconjN1 n) = (c.rho n)⁻¹ := by rw [hzn, map_inv]
  rw [c.rho_zconj] at hρn
  have hb : (c.rho n).2 = (c.rho n).1⁻¹ := congrArg Prod.fst hρn
  have hmem1 : ((c.rho n).1, (1 : MulAut ↥E)) ∈ c.Rhat (Rs ⊓ c.N1) := ha r hr hrdef.symm
  obtain ⟨u', hu'R, hu'⟩ := c.mem_Rhat.1 hmem1
  obtain ⟨u, hudef⟩ : ∃ u : G, u = (u' : G) := ⟨_, rfl⟩
  rw [← hudef] at hu'R
  have hzu : z * u * z⁻¹ ∈ Rs ⊓ c.N1 := hR.z_conj_R hu'R
  have hρu'' : c.rho (c.zconjN1 u') = (1, (c.rho n).1) := by
    rw [c.rho_zconj, hu']
  have hk0 : c.rho (n⁻¹ * (u' * (c.zconjN1 u')⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, hu', hρu'']
    ext
    · simp
    · simp [hb]
  have hk0coe : ((n⁻¹ * (u' * (c.zconjN1 u')⁻¹) : ↥c.N1) : G) =
      r⁻¹ * (u * (z * u * z⁻¹)⁻¹) := by
    rw [hudef]
    rfl
  have hk0R : r⁻¹ * (u * (z * u * z⁻¹)⁻¹) ∈ Rs ⊓ c.N1 :=
    mul_mem (inv_mem hr) (mul_mem hu'R (inv_mem hzu))
  have hk0KR : r⁻¹ * (u * (z * u * z⁻¹)⁻¹) ∈ c.KR := by
    rw [← hk0coe]
    exact c.mem_KR.2 ⟨(n⁻¹ * (u' * (c.zconjN1 u')⁻¹)).2, hk0⟩
  obtain ⟨k, hkdef⟩ : ∃ k : G, k = r⁻¹ * (u * (z * u * z⁻¹)⁻¹) := ⟨_, rfl⟩
  rw [← hkdef] at hk0R hk0KR
  have hkZ : k ∈ c.Zs := hR.R_inf_KR_le ⟨hk0R, hk0KR⟩
  have hu_eq : u * z * u⁻¹ = r * k * z := by
    rw [hkdef]
    group
  have hrk : r * k = k * r := c.Zs_comm_N1 hkZ hrN
  have hrkr : r * k * r⁻¹ = k := by
    rw [hrk]
    group
  have h_inv : r * k * z * (r * k * z) = 1 := by
    rw [← hu_eq]
    calc u * z * u⁻¹ * (u * z * u⁻¹) = u * (z * z) * u⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hkz : k * z * (k * z) = 1 := by
    calc k * z * (k * z) = k * (z * k * z) := by group
      _ = (r * k * r⁻¹) * (z * k * z) := by rw [hrkr]
      _ = r * k * (r⁻¹ * z) * k * z := by group
      _ = r * k * (z * r) * k * z := by rw [hzr']
      _ = r * k * z * (r * k * z) := by group
      _ = 1 := h_inv
  have hyrz : r * z = y := by
    rw [hrdef]
    calc y * z * z = y * (z * z) := by group
      _ = y := by rw [hzz, mul_one]
  rcases c.eq_one_or_t_of_sq hkZ hkz with hk | hk
  · refine ⟨u, hu'R, ?_⟩
    rw [hu_eq, hk, mul_one, hyrz]
  · have hαR : α ∈ Rs ⊓ c.N1 := hR.Zs_le_R c.alpha_mem_Zs
    refine ⟨α * u, mul_mem hαR hu'R, ?_⟩
    have hαr : r * α = α * r := c.Zs_comm_N1 c.alpha_mem_Zs hrN
    have hαt : α * t = t * α := c.h.t_comm_S α c.hα.mem
    have hαrt : α * (r * t) * α⁻¹ = r * t := by
      have e : α * (r * t) = (r * t) * α := by
        calc α * (r * t) = (α * r) * t := by group
          _ = (r * α) * t := by rw [hαr]
          _ = r * (α * t) := by group
          _ = r * (t * α) := by rw [hαt]
          _ = (r * t) * α := by group
      rw [e]
      group
    calc y = r * z := hyrz.symm
      _ = r * (t * t) * z := by rw [c.h.t_sq, mul_one]
      _ = (r * t) * (t * z) := by group
      _ = (α * (r * t) * α⁻¹) * (α * z * α⁻¹) := by rw [hαrt, ← c.t_mul_z]
      _ = α * (r * t * z) * α⁻¹ := by group
      _ = α * (u * z * u⁻¹) * α⁻¹ := by rw [hu_eq, hk]
      _ = α * u * z * (α * u)⁻¹ := by group

theorem IsRs.Rhat_prodB {Rs : Subgroup G} (hR : c.IsRs Rs)
    (hB : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range) :
    ∃ S₁ S₂ : Subgroup (MulAut ↥E), IsPGroup 2 S₁ ∧ IsPGroup 2 S₂ ∧
      (∀ P : Subgroup (MulAut ↥E), IsPGroup 2 P → S₁ ≤ P → P ≤ S₁) ∧
      (∀ P : Subgroup (MulAut ↥E), IsPGroup 2 P → S₂ ≤ P → P ≤ S₂) ∧
      c.Rhat (Rs ⊓ c.N1) = S₁.prod S₂ := by
  have hrange : c.rho.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    exact hB a b
  obtain ⟨heq, h1, h2, -, -, h5, h6⟩ :=
    eq_prod_of_max (Θ₁ := ⊤) (Θ₂ := ⊤) (Rhat_pgroup hR.R_pgroup)
      (fun _ _ => ⟨mem_top _, mem_top _⟩)
      (fun P hP _ hle => hR.Rhat_max P hP (by rw [hrange]; exact le_top) hle)
  exact ⟨_, _, h1, h2, fun P hP hle => h5 P hP le_top hle,
    fun P hP hle => h6 P hP le_top hle, heq⟩

variable (c)

theorem hbigB (hB : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range) (hE : EFacts614 E t) :
    ∀ ψ : ↥c.rho.range, ψ * ψ = 1 →
      2 ^ 9 ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set ↥c.rho.range)) := by
  intro ψ hψ
  have hx : ∀ x : MulAut ↥E × MulAut ↥E, x ∈ c.rho.range := fun x => by
    simpa using hB x.1 x.2
  have hmap : (Subgroup.centralizer ({ψ} : Set ↥c.rho.range)).map c.rho.range.subtype =
      Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E)) := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have h1 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hγ)
      exact mem_centralizer_singleton_iff.2 h1
    · intro hx'
      refine ⟨⟨x, hx x⟩, mem_centralizer_singleton_iff.2 ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hx')
  have hcardEq : Nat.card ↥(Subgroup.centralizer ({ψ} : Set ↥c.rho.range)) =
      Nat.card ↥(Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E))) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (f := c.rho.range.subtype) Subtype.val_injective).symm
  have hprod : Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E)) =
      (Subgroup.centralizer ({ψ.1.1} : Set (MulAut ↥E))).prod
        (Subgroup.centralizer ({ψ.1.2} : Set (MulAut ↥E))) := by
    ext x
    simp only [mem_centralizer_singleton_iff, Subgroup.mem_prod, Prod.ext_iff, Prod.fst_mul,
      Prod.snd_mul]
  have h0 : ψ.1 * ψ.1 = 1 := congrArg Subtype.val hψ
  have ha : ψ.1.1 * ψ.1.1 = 1 := congrArg Prod.fst h0
  have hb : ψ.1.2 * ψ.1.2 = 1 := congrArg Prod.snd h0
  have h1 := hE.cent_dvd ψ.1.1 ha
  have h2 := hE.cent_dvd ψ.1.2 hb
  rw [hcardEq, hprod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  exact (show (2 : ℕ) ^ 9 ∣ 32 * 32 by norm_num).trans (Nat.mul_dvd_mul h1 h2)

theorem caseB_final (hB : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range) (hE : EFacts614 E t)
    (hT : Nat.card T ≤ 512) :
    ∃ Rs R : Subgroup G, IsPGroup 2 Rs ∧ R ≤ Rs ∧ R.relIndex Rs = 2 ∧ z ∈ Rs ∧ z ∉ R ∧
      (∀ g : G, g * z * g⁻¹ ∈ Rs → ∃ r ∈ Rs, g * z * g⁻¹ = r * z * r⁻¹) ∧
      ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G)) := by
  obtain ⟨Rs, hR, hTRs⟩ := c.exists_isRs
  have hA : ∀ r : G, ∀ hr : r ∈ Rs ⊓ c.N1,
      ((c.rho ⟨r, hr.2⟩).1, (1 : MulAut ↥E)) ∈ c.Rhat (Rs ⊓ c.N1) := by
    obtain ⟨S₁, S₂, -, -, -, -, hRh⟩ := hR.Rhat_prodB hB
    intro r hr
    have hmem : c.rho ⟨r, hr.2⟩ ∈ c.Rhat (Rs ⊓ c.N1) := c.mem_Rhat.2 ⟨⟨r, hr.2⟩, hr, rfl⟩
    rw [hRh] at hmem ⊢
    exact ⟨hmem.1, S₂.one_mem⟩
  have hbig := c.hbigB hB hE
  refine ⟨Rs, Rs ⊓ c.N1, hR.pgroup, inf_le_left, hR.relIndex_R.1, hR.z_mem, hR.relIndex_R.2,
    ?_, ?_⟩
  · intro g hg
    have hgg : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [c.h.z_sq]; group
    by_cases hgR : g * z * g⁻¹ ∈ Rs ⊓ c.N1
    · exact (hR.not_conj_z_of_mem_R hbig hT hgR hgg ⟨g, rfl⟩).elim
    · obtain ⟨u, hu, hu_eq⟩ := hR.exists_conj_of_not_mem_R hg hgR hgg (fun r hr _ => hA r hr)
      exact ⟨u, hu.1, hu_eq⟩
  · have hcard : Nat.card T ≤ Nat.card ↥(Rs ⊓ centralizer ({z} : Set G)) :=
      Subgroup.card_le_of_le (le_inf hTRs c.h.oe.cfg.T_le)
    exact c.h.relIndex_cent_z_odd hR.pgroup hcard

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
