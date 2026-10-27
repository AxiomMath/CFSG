module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10B
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem m11AutInv_commutator (V : Subgroup G) : m11AutInv V ⁅V, V⁆ := by
  have key : Subgroup.map V.subtype ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⁅V, V⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro α v hv
  rw [← key] at hv ⊢
  obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp hv
  have huv' : u = v := Subtype.ext huv
  rw [huv'] at hu
  refine Subgroup.mem_map.mpr ⟨α v, ?_, rfl⟩
  have h1 : Subgroup.map α.toMonoidHom ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ =
      ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ α.surjective]
  rw [← h1]
  exact Subgroup.mem_map.mpr ⟨v, hu, rfl⟩

theorem r10_fix_modZ [Finite G] {R Z : Subgroup G} {ρ : G} (hZR : Z ≤ R)
    (hZc : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z) (hρZ : ∀ z ∈ Z, ρ * z * ρ⁻¹ ∈ Z)
    (hfix : ∀ r ∈ R, ρ * r = r * ρ → r = 1) {r : G} (hr : r ∈ R)
    (hmod : ρ * r * ρ⁻¹ * r⁻¹ ∈ Z) : r ∈ Z := by
  have hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a ha b (hZR hb)
  let ψ : ↥Z →* ↥Z := MonoidHom.mk'
    (fun z => ⟨(z : G) * (ρ * (z : G) * ρ⁻¹)⁻¹, Z.mul_mem z.2 (Z.inv_mem (hρZ _ z.2))⟩)
    (fun z z' => by
      apply Subtype.ext
      have ha' : ρ * (z : G) * ρ⁻¹ ∈ Z := hρZ _ z.2
      have hb' : ρ * (z' : G) * ρ⁻¹ ∈ Z := hρZ _ z'.2
      have hA : ρ * ((z : G) * (z' : G)) * ρ⁻¹ = (ρ * (z : G) * ρ⁻¹) * (ρ * (z' : G) * ρ⁻¹) := by
        group
      have c1 : (ρ * (z' : G) * ρ⁻¹)⁻¹ * (ρ * (z : G) * ρ⁻¹)⁻¹ =
          (ρ * (z : G) * ρ⁻¹)⁻¹ * (ρ * (z' : G) * ρ⁻¹)⁻¹ :=
        hcomm _ (Z.inv_mem hb') _ (Z.inv_mem ha')
      have c2 : (z' : G) * (ρ * (z : G) * ρ⁻¹)⁻¹ = (ρ * (z : G) * ρ⁻¹)⁻¹ * (z' : G) :=
        hcomm _ z'.2 _ (Z.inv_mem ha')
      show (z : G) * (z' : G) * (ρ * ((z : G) * (z' : G)) * ρ⁻¹)⁻¹ =
        (z : G) * (ρ * (z : G) * ρ⁻¹)⁻¹ * ((z' : G) * (ρ * (z' : G) * ρ⁻¹)⁻¹)
      rw [hA, mul_inv_rev, c1]
      calc (z : G) * (z' : G) * ((ρ * (z : G) * ρ⁻¹)⁻¹ * (ρ * (z' : G) * ρ⁻¹)⁻¹)
          = (z : G) * ((z' : G) * (ρ * (z : G) * ρ⁻¹)⁻¹) * (ρ * (z' : G) * ρ⁻¹)⁻¹ := by group
        _ = (z : G) * ((ρ * (z : G) * ρ⁻¹)⁻¹ * (z' : G)) * (ρ * (z' : G) * ρ⁻¹)⁻¹ := by rw [c2]
        _ = (z : G) * (ρ * (z : G) * ρ⁻¹)⁻¹ * ((z' : G) * (ρ * (z' : G) * ρ⁻¹)⁻¹) := by group)
  have hker : ∀ z : ↥Z, ψ z = 1 → z = 1 := by
    intro z hz
    have h1 : (z : G) * (ρ * (z : G) * ρ⁻¹)⁻¹ = 1 := congrArg Subtype.val hz
    have h2 : (z : G) = ρ * (z : G) * ρ⁻¹ := mul_inv_eq_one.mp h1
    have h3 : ρ * (z : G) = (z : G) * ρ := by
      calc ρ * (z : G) = (ρ * (z : G) * ρ⁻¹) * ρ := by group
        _ = (z : G) * ρ := by rw [← h2]
    exact Subtype.ext (hfix _ (hZR z.2) h3)
  have hψinj : Function.Injective ψ := (injective_iff_map_eq_one ψ).mpr hker
  obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.mp hψinj ⟨ρ * r * ρ⁻¹ * r⁻¹, hmod⟩
  have h1 : (z : G) * (ρ * (z : G) * ρ⁻¹)⁻¹ = ρ * r * ρ⁻¹ * r⁻¹ := congrArg Subtype.val hz
  have e1 : ρ * r * ρ⁻¹ = (ρ * r * ρ⁻¹ * r⁻¹) * r := by group
  have e2 : (z : G) = (ρ * r * ρ⁻¹ * r⁻¹) * (ρ * (z : G) * ρ⁻¹) := by
    calc (z : G) = ((z : G) * (ρ * (z : G) * ρ⁻¹)⁻¹) * (ρ * (z : G) * ρ⁻¹) := by group
      _ = (ρ * r * ρ⁻¹ * r⁻¹) * (ρ * (z : G) * ρ⁻¹) := by rw [h1]
  have e3 : ρ * (r * (z : G)) * ρ⁻¹ = r * (z : G) := by
    calc ρ * (r * (z : G)) * ρ⁻¹ = (ρ * r * ρ⁻¹) * (ρ * (z : G) * ρ⁻¹) := by group
      _ = ((ρ * r * ρ⁻¹ * r⁻¹) * r) * (ρ * (z : G) * ρ⁻¹) := by rw [← e1]
      _ = (r * (ρ * r * ρ⁻¹ * r⁻¹)) * (ρ * (z : G) * ρ⁻¹) := by rw [hZc _ hmod r hr]
      _ = r * ((ρ * r * ρ⁻¹ * r⁻¹) * (ρ * (z : G) * ρ⁻¹)) := by group
      _ = r * (z : G) := by rw [← e2]
  have e4 : r * (z : G) = 1 :=
    hfix _ (R.mul_mem hr (hZR z.2)) (mul_inv_eq_iff_eq_mul.mp e3)
  rw [eq_inv_of_mul_eq_one_left e4]
  exact Z.inv_mem z.2

end Abstract

section R10C

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem r10_comm_V_le_R (h : L41GPh8 t L S x₁ x₂ lam rho) :
    ⁅l41V S t x₁ x₂, l41V S t x₁ x₂⁆ ≤ l41R t x₁ x₂ rho := by
  obtain ⟨φ, -, hker⟩ := m11_quot_V_R h
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h1 : φ (⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩ * ⟨g₁, hg₁⟩⁻¹ * ⟨g₂, hg₂⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (φ ⟨g₁, hg₁⟩) (φ ⟨g₂, hg₂⟩)]
    group
  have h2 : (⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩ * ⟨g₁, hg₁⟩⁻¹ * ⟨g₂, hg₂⟩⁻¹ : ↥(l41V S t x₁ x₂)) ∈
      (l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂) := by
    rw [← hker]
    exact h1
  exact Subgroup.mem_subgroupOf.mp h2

theorem r10_comm_mem (h : L41GPh8 t L S x₁ x₂ lam rho) {u v : G} (hu : u ∈ l41R t x₁ x₂ rho)
    (hv : v ∈ l41R t x₁ x₂ rho) : u * v * u⁻¹ * v⁻¹ ∈ fourGrp x₁ x₂ :=
  h.rfacts.comm_le (Subgroup.commutator_mem_commutator hu hv)

theorem r10_cent_lam_le (h : L41GPh9 t L S x₁ x₂ lam rho)
    (hcommZ : ∀ z ∈ fourGrp x₁ x₂, ∃ r ∈ l41R t x₁ x₂ rho, ∃ s ∈ l41R t x₁ x₂ rho,
      r * s * r⁻¹ * s⁻¹ = z)
    {c : G} (hc : c ∈ l41R t x₁ x₂ rho) (hcl : lam * c = c * lam) :
    c ∈ ⁅l41V S t x₁ x₂, l41V S t x₁ x₂⁆ := by
  have hρ3 : rho * rho * rho = 1 := by
    have := n4_rho_cube h.toCtx0
    rwa [pow_succ, pow_two] at this
  have hRV := m11_R_le_V h.toL41GPh8
  have hlamV := m11_lam_mem_V h.toL41GPh8
  have hZR := h.rfacts.fourGrp_le
  have hZc := h.rfacts.fourGrp_central
  have hρZ : ∀ z ∈ fourGrp x₁ x₂, rho * z * rho⁻¹ ∈ fourGrp x₁ x₂ := fun z hz =>
    m11_rho_conj_F2 h.toL41GPh8 hz
  have hZV : fourGrp x₁ x₂ ≤ ⁅l41V S t x₁ x₂, l41V S t x₁ x₂⁆ := by
    intro z hz
    obtain ⟨r, hr, s, hs, rfl⟩ := hcommZ z hz
    exact Subgroup.commutator_mem_commutator (hRV hr) (hRV hs)
  obtain ⟨a₁, ha₁def⟩ : ∃ a₁, a₁ = rho * c * rho⁻¹ := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂def⟩ : ∃ a₂, a₂ = rho * a₁ * rho⁻¹ := ⟨_, rfl⟩
  have ha₁ : a₁ ∈ l41R t x₁ x₂ rho := by rw [ha₁def]; exact m11_rho_conj_R h.toL41GPh8 hc
  have ha₂ : a₂ ∈ l41R t x₁ x₂ rho := by rw [ha₂def]; exact m11_rho_conj_R h.toL41GPh8 ha₁
  have F1 : rho * a₂ * rho⁻¹ = c := by
    rw [ha₂def, ha₁def]
    exact r10_conj3 hρ3 c
  have F2 : lam * a₁ * lam⁻¹ = a₂ := by
    have hl1 : lam * c * lam⁻¹ = c := by rw [hcl]; group
    have hl2 : lam * rho⁻¹ * lam⁻¹ = rho := by
      calc lam * rho⁻¹ * lam⁻¹ = (lam * rho * lam⁻¹)⁻¹ := by group
        _ = rho := by rw [h.lam_rho, inv_inv]
    have e : rho * rho = rho⁻¹ := eq_inv_of_mul_eq_one_left hρ3
    calc lam * a₁ * lam⁻¹ = (lam * rho * lam⁻¹) * (lam * c * lam⁻¹) * (lam * rho⁻¹ * lam⁻¹) := by
          rw [ha₁def]; group
      _ = rho⁻¹ * c * rho := by rw [h.lam_rho, hl1, hl2]
      _ = (rho * rho) * c * (rho * rho)⁻¹ := by rw [e, inv_inv]
      _ = a₂ := by rw [ha₂def, ha₁def]; group
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = c * a₁ * a₂ := ⟨_, rfl⟩
  have hνR : ν ∈ l41R t x₁ x₂ rho := by
    rw [hνdef]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc ha₁) ha₂
  have F3 : rho * ν * rho⁻¹ = a₁ * a₂ * c := by
    calc rho * ν * rho⁻¹ = (rho * c * rho⁻¹) * (rho * a₁ * rho⁻¹) * (rho * a₂ * rho⁻¹) := by
          rw [hνdef]; group
      _ = a₁ * a₂ * c := by rw [← ha₁def, ← ha₂def, F1]
  have F4 : rho * ν * rho⁻¹ * ν⁻¹ ∈ fourGrp x₁ x₂ := by
    have := r10_comm_mem h.toL41GPh8 (Subgroup.mul_mem _ ha₁ ha₂) hc
    have e : rho * ν * rho⁻¹ * ν⁻¹ = a₁ * a₂ * c * (a₁ * a₂)⁻¹ * c⁻¹ := by
      rw [F3, hνdef]; group
    rw [e]
    exact this
  have hν : ν ∈ fourGrp x₁ x₂ :=
    r10_fix_modZ hZR hZc hρZ (fun r hr hρ => m11_fix_R h.toL41GPh8 hr hρ) hνR F4
  have hs : a₂⁻¹ * a₂⁻¹ ∈ fourGrp x₁ x₂ := h.rfacts.sq_mem _ (Subgroup.inv_mem _ ha₂)
  have F5 : a₁ * a₂ * c = ν := by
    calc a₁ * a₂ * c = c⁻¹ * (c * a₁ * a₂) * c := by group
      _ = c⁻¹ * ν * c := by rw [hνdef]
      _ = ν := by rw [mul_assoc, hZc ν hν c hc, inv_mul_cancel_left]
  have F6 : a₁ * a₂⁻¹ * c = ν * (a₂⁻¹ * a₂⁻¹) := by
    calc a₁ * a₂⁻¹ * c = (a₁ * a₂ * c) * (c⁻¹ * (a₂⁻¹ * a₂⁻¹) * c) := by group
      _ = ν * (a₂⁻¹ * a₂⁻¹) := by
          rw [F5, mul_assoc c⁻¹, hZc _ hs c hc, inv_mul_cancel_left]
  have hζ : a₁ * a₂⁻¹ * c ∈ fourGrp x₁ x₂ := by
    rw [F6]
    exact Subgroup.mul_mem _ hν hs
  have F7 : c = (lam * a₁ * lam⁻¹ * a₁⁻¹) * (a₁ * a₂⁻¹ * c) := by
    rw [F2]
    group
  rw [F7]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hlamV (hRV ha₁)) (hZV hζ)

theorem r10_center_derived (h : L41GPh9 t L S x₁ x₂ lam rho)
    (hcommZ : ∀ z ∈ fourGrp x₁ x₂, ∃ r ∈ l41R t x₁ x₂ rho, ∃ s ∈ l41R t x₁ x₂ rho,
      r * s * r⁻¹ * s⁻¹ = z)
    (hcp : ∀ d₁ ∈ l41R t x₁ x₂ rho, ∀ d₂ ∈ l41R t x₁ x₂ rho, d₁ * d₂ ≠ d₂ * d₁ →
      ∀ c ∈ l41R t x₁ x₂ rho, c * d₁ = d₁ * c → c * d₂ = d₂ * c → c ∈ fourGrp x₁ x₂)
    (hnab : ∃ d₁ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G),
      ∃ d₂ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G), d₁ * d₂ ≠ d₂ * d₁) :
    ⁅l41V S t x₁ x₂, l41V S t x₁ x₂⁆ ⊓ (l41V S t x₁ x₂ ⊓
      centralizer ((⁅l41V S t x₁ x₂, l41V S t x₁ x₂⁆ : Subgroup G) : Set G)) = fourGrp x₁ x₂ := by
  have hRV := m11_R_le_V h.toL41GPh8
  have hVR := r10_comm_V_le_R h.toL41GPh8
  have hZR := h.rfacts.fourGrp_le
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV', hg2⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨-, hgc⟩ := Subgroup.mem_inf.mp hg2
    obtain ⟨d₁, hd₁, d₂, hd₂, hne⟩ := hnab
    obtain ⟨hd₁R, hd₁c⟩ := Subgroup.mem_inf.mp hd₁
    obtain ⟨hd₂R, hd₂c⟩ := Subgroup.mem_inf.mp hd₂
    have hd₁V' := r10_cent_lam_le h hcommZ hd₁R
      (Subgroup.mem_centralizer_singleton_iff.mp hd₁c).symm
    have hd₂V' := r10_cent_lam_le h hcommZ hd₂R
      (Subgroup.mem_centralizer_singleton_iff.mp hd₂c).symm
    exact hcp d₁ hd₁R d₂ hd₂R hne g (hVR hgV')
      (Subgroup.mem_centralizer_iff.mp hgc d₁ hd₁V').symm
      (Subgroup.mem_centralizer_iff.mp hgc d₂ hd₂V').symm
  · intro z hz
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_inf.mpr ⟨hRV (hZR hz),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩⟩
    · obtain ⟨r, hr, s, hs, rfl⟩ := hcommZ z hz
      exact Subgroup.commutator_mem_commutator (hRV hr) (hRV hs)
    · exact (h.rfacts.fourGrp_central z hz v (hVR hv)).symm

theorem r10_cent_mul (h : L41GPh8 t L S x₁ x₂ lam rho) {r k : G}
    (hr : r ∈ l41R t x₁ x₂ rho) (hcent : ∀ x ∈ fourGrp x₁ x₂, r * k * x = x * (r * k)) :
    ∀ x ∈ fourGrp x₁ x₂, k * x = x * k := by
  intro x hx
  have hrx : r * x = x * r := (h.rfacts.fourGrp_central x hx r hr).symm
  apply mul_left_cancel (a := r)
  calc r * (k * x) = r * k * x := (mul_assoc _ _ _).symm
    _ = x * (r * k) := hcent x hx
    _ = (x * r) * k := (mul_assoc _ _ _).symm
    _ = (r * x) * k := by rw [hrx]
    _ = r * (x * k) := mul_assoc _ _ _

theorem r10_cent_V_F2 (h : L41GPh9 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) = l41F t x₁ x₂ rho := by
  have htF2 : ∀ x ∈ fourGrp x₁ x₂, t * x = x * t := fun x hx =>
    m13_t_comm_base h.toL41GPh5 (m11_fourGrp_le_B x₁ x₂ hx)
  have hρ3 := n4_rho_cube h.toCtx0
  have htl : t * lam = lam * t := m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  have hfix : ∀ x ∈ fourGrp x₁ x₂, rho * x = x * rho → x = 1 := fun x hx hxρ =>
    m11_fix_R h.toL41GPh8 (h.rfacts.fourGrp_le hx) hxρ
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgc' : ∀ x ∈ fourGrp x₁ x₂, g * x = x * g := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hgc x hx).symm
    obtain ⟨r, hr, hcases⟩ := m11_mem_V_cases h.toL41GPh8 hgV
    rcases hcases with hg1 | hg1 | hg1 | hg1
    · rw [hg1]
      exact Subgroup.mem_sup_left hr
    · rw [hg1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    · exfalso
      rw [hg1] at hgc'
      exact m11_F2_ne_bot h.toCtx0 (m11_eq_bot_of_inverting_centralizes _
        (fun x hx => m11_rho_conj_F2 h.toL41GPh8 hx) hρ3 h.lam_rho hfix
        (r10_cent_mul h.toL41GPh8 hr hgc'))
    · exfalso
      rw [hg1, htl] at hgc'
      exact m11_F2_ne_bot h.toCtx0 (m11_eq_bot_of_inverting_centralizes _
        (fun x hx => m11_rho_conj_F2 h.toL41GPh8 hx) hρ3 (m11_lamt_rho h.toL41GPh5) hfix
        (r10_cent_mul h.toL41GPh8 hr hgc'))
  · have hFc : l41F t x₁ x₂ rho ≤ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      refine sup_le (fun r hr => Subgroup.mem_centralizer_iff.mpr fun x hx => ?_) ?_
      · exact h.rfacts.fourGrp_central x hx r hr
      · refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
        exact (htF2 x hx).symm
    exact fun g hg => Subgroup.mem_inf.mpr ⟨m11_F_le_V h.toL41GPh8 hg, hFc hg⟩

theorem r10_autInv_Z (h : L41GPh9 t L S x₁ x₂ lam rho)
    (hcommZ : ∀ z ∈ fourGrp x₁ x₂, ∃ r ∈ l41R t x₁ x₂ rho, ∃ s ∈ l41R t x₁ x₂ rho,
      r * s * r⁻¹ * s⁻¹ = z)
    (hcp : ∀ d₁ ∈ l41R t x₁ x₂ rho, ∀ d₂ ∈ l41R t x₁ x₂ rho, d₁ * d₂ ≠ d₂ * d₁ →
      ∀ c ∈ l41R t x₁ x₂ rho, c * d₁ = d₁ * c → c * d₂ = d₂ * c → c ∈ fourGrp x₁ x₂)
    (hnab : ∃ d₁ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G),
      ∃ d₂ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G), d₁ * d₂ ≠ d₂ * d₁) :
    m11AutInv (l41V S t x₁ x₂) (fourGrp x₁ x₂) := by
  have hV'V : ⁅l41V S t x₁ x₂, l41V S t x₁ x₂⁆ ≤ l41V S t x₁ x₂ :=
    (r10_comm_V_le_R h.toL41GPh8).trans (m11_R_le_V h.toL41GPh8)
  have h1 := (m11AutInv_commutator (l41V S t x₁ x₂)).inf
    ((m11AutInv_commutator (l41V S t x₁ x₂)).cent hV'V)
  rwa [r10_center_derived h hcommZ hcp hnab] at h1

theorem r10_autInv_F (h : L41GPh9 t L S x₁ x₂ lam rho)
    (hcommZ : ∀ z ∈ fourGrp x₁ x₂, ∃ r ∈ l41R t x₁ x₂ rho, ∃ s ∈ l41R t x₁ x₂ rho,
      r * s * r⁻¹ * s⁻¹ = z)
    (hcp : ∀ d₁ ∈ l41R t x₁ x₂ rho, ∀ d₂ ∈ l41R t x₁ x₂ rho, d₁ * d₂ ≠ d₂ * d₁ →
      ∀ c ∈ l41R t x₁ x₂ rho, c * d₁ = d₁ * c → c * d₂ = d₂ * c → c ∈ fourGrp x₁ x₂)
    (hnab : ∃ d₁ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G),
      ∃ d₂ ∈ l41R t x₁ x₂ rho ⊓ centralizer ({lam} : Set G), d₁ * d₂ ≠ d₂ * d₁) :
    m11AutInv (l41V S t x₁ x₂) (l41F t x₁ x₂ rho) := by
  have hZV : fourGrp x₁ x₂ ≤ l41V S t x₁ x₂ :=
    h.rfacts.fourGrp_le.trans (m11_R_le_V h.toL41GPh8)
  have h1 := (r10_autInv_Z h hcommZ hcp hnab).cent hZV
  rwa [r10_cent_V_F2 h] at h1

end R10C

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
