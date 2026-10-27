module

public import CFSG.LargeExtraspecial.S10SixG
public import Certificates.Certificate19951
public import CFSG.LargeExtraspecial.S10Block

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem σ₁_cube : σ₁ * σ₁ * σ₁ = 1 :=
  Certificates.certificate19951.1
theorem σ₂_cube : σ₂ * σ₂ * σ₂ = 1 :=
  Certificates.certificate19951.2.1
theorem σ₁_σ₂_comm : σ₁ * σ₂ = σ₂ * σ₁ :=
  Certificates.certificate19951.2.2.1
theorem τ₁_σ₁ : τ₁ * σ₁ = σ₁ * σ₁ * τ₁ :=
  Certificates.certificate19951.2.2.2.1
theorem τ₁_σ₂ : τ₁ * σ₂ = σ₂ * τ₁ :=
  Certificates.certificate19951.2.2.2.2.1
theorem τ₂_σ₁ : τ₂ * σ₁ = σ₁ * τ₂ :=
  Certificates.certificate19951.2.2.2.2.2.1
theorem τ₂_σ₂ : τ₂ * σ₂ = σ₂ * σ₂ * τ₂ :=
  Certificates.certificate19951.2.2.2.2.2.2.1
theorem τ₁_comm_σ₂ : τ₁⁻¹ * (σ₂ * τ₁ * σ₂⁻¹) = 1 :=
  Certificates.certificate19951.2.2.2.2.2.2.2

theorem conj_inv_aux {X : Type*} [Group X] {x c : X} (hx : x * x = 1) (hc : c * c = 1) :
    x * (x⁻¹ * c) * x⁻¹ * (x⁻¹ * c)⁻¹ = ((x⁻¹ * c) * (x⁻¹ * c))⁻¹ := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_left hc
  simp only [mul_inv_rev, hx', hc', mul_assoc]
  rw [← mul_assoc x x, hx, one_mul]

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem mem_Lbar_of_comm_two (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {x y : S.O} (hxL : x ∈ S.Lbar g) (hyL : y ∈ S.Lbar g)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) (hπy : F.π ⟨y, Lbar_le_Rbar X.ht hyL⟩ = τ₂)
    {n : S.O} (hn : n ∈ Nbar S g t) (hcx : x * n * x⁻¹ * n⁻¹ ∈ zpowers t)
    (hcy : y * n * y⁻¹ * n⁻¹ ∈ zpowers t) : n ∈ S.Lbar g := by
  have := X.nqHyp hCE
  have hxt : x * t = t * x := S4.Lbar_comm S X.haQ hxL X.ht
  have hyt : y * t = t * y := S4.Lbar_comm S X.haQ hyL X.ht
  have hA : ∀ a ∈ S.Lbar g ⊓ Nbar S g t, a * n * a⁻¹ * n⁻¹ ∈ zpowers t :=
    fun a ha => NQHyp.comm a ha.2 n hn
  have hxR := Lbar_le_Rbar X.ht hxL
  have hyR := Lbar_le_Rbar X.ht hyL
  have hall : ∀ l ∈ S.Lbar g, l * n * l⁻¹ * n⁻¹ ∈ zpowers t := by
    intro l hl
    have hlR := Lbar_le_Rbar X.ht hl
    have hst := F.π_mem_stabA hl
    rw [mem_stabA, act_E00_iff] at hst
    rcases hst with h | h | h | h
    · exact hA l ⟨hl, (F.ker _).mp h⟩
    · have hm : x⁻¹ * l ∈ S.Lbar g ⊓ Nbar S g t := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hxL) hl,
          (F.ker ⟨x⁻¹ * l, mul_mem (inv_mem hxR) hlR⟩).mp ?_⟩
        have e : (⟨x⁻¹ * l, mul_mem (inv_mem hxR) hlR⟩ : Rbar S g t) =
            (⟨x, hxR⟩ : Rbar S g t)⁻¹ * ⟨l, hlR⟩ := Subtype.ext (by simp)
        rw [e, map_mul, map_inv, hπx, h, inv_mul_cancel]
      have := comm_mod_mul hxt hcx (hA _ hm)
      rwa [mul_inv_cancel_left] at this
    · have hm : y⁻¹ * l ∈ S.Lbar g ⊓ Nbar S g t := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hyL) hl,
          (F.ker ⟨y⁻¹ * l, mul_mem (inv_mem hyR) hlR⟩).mp ?_⟩
        have e : (⟨y⁻¹ * l, mul_mem (inv_mem hyR) hlR⟩ : Rbar S g t) =
            (⟨y, hyR⟩ : Rbar S g t)⁻¹ * ⟨l, hlR⟩ := Subtype.ext (by simp)
        rw [e, map_mul, map_inv, hπy, h, inv_mul_cancel]
      have := comm_mod_mul hyt hcy (hA _ hm)
      rwa [mul_inv_cancel_left] at this
    · have hm : (x * y)⁻¹ * l ∈ S.Lbar g ⊓ Nbar S g t := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (mul_mem hxL hyL)) hl,
          (F.ker ⟨(x * y)⁻¹ * l, mul_mem (inv_mem (mul_mem hxR hyR)) hlR⟩).mp ?_⟩
        have e : (⟨(x * y)⁻¹ * l, mul_mem (inv_mem (mul_mem hxR hyR)) hlR⟩ : Rbar S g t) =
            ((⟨x, hxR⟩ : Rbar S g t) * ⟨y, hyR⟩)⁻¹ * ⟨l, hlR⟩ := Subtype.ext (by simp)
        rw [e, map_mul, map_inv, map_mul, hπx, hπy, h, inv_mul_cancel]
      have hxy : (x * y) * t = t * (x * y) := by
        rw [mul_assoc, hyt, ← mul_assoc, hxt, mul_assoc]
      have := comm_mod_mul hxy (comm_mod_mul hxt hcx hcy) (hA _ hm)
      rwa [mul_inv_cancel_left] at this
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    rw [X.h4]
    norm_num
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  have h1R : S.ρ (1 : S.M) ∈ Rbar S g t := by
    rw [map_one]
    exact one_mem _
  have := mem_Lbar_of_comm_mem X.H X.C X.ht X.ht1 X.hVQ X.pairGen (X.N0 hCE) h3 hk hb h1R hn
    (by simpa using hall)
  simpa using this

theorem finrank_nq_eq (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) [NQHyp S g t] :
    finrank (ZMod 2) (NQ S g t) = 2 * finrank (ZMod 2) (nqSub S g t (S.Lbar g)) := by
  obtain ⟨k, hk, -, hb⟩ := X.exists_pair
  have h1R : S.ρ (1 : S.M) ∈ Rbar S g t := by
    rw [map_one]
    exact one_mem _
  have hb' : (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa (((1 : S.M) : G) * g) := by
    simpa using hb
  have hgen := X.pairGen 1 k h1R hk hb'
  have e1 : S.Lbar (((1 : S.M) : G) * g) = S.Lbar g := by simp
  have hinf : S.Lbar g ⊓ S.Lbar ((k : G) * g) = zpowers t := by
    rw [← e1]
    exact timmesfeld_6_5_inf X.H X.ht h1R hk hgen (X.N0 hCE) X.C X.ht1 X.hVQ
  have hprod : ∀ n : Nbar S g t, ∃ x y : Nbar S g t,
      (x : S.O) ∈ S.Lbar g ∧ (y : S.O) ∈ S.Lbar ((k : G) * g) ∧ n = x * y := by
    intro n
    obtain ⟨y₁, hy₁, y₂, hy₂, e⟩ := exists_mul_of_pair X.H X.ht h1R hk hgen (X.N0 hCE) n.2
    refine ⟨⟨y₁, hy₁.2⟩, ⟨y₂, hy₂.2⟩, ?_, hy₂.1, Subtype.ext e⟩
    rw [← e1]
    exact hy₁.1
  have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_nqSub hprod hinf)
  have hmap := nqSub_map_nqHom (g₀ := g) (g₁ := (k : G) * g) hk rfl
  have h2 : finrank (ZMod 2) (nqSub S g t (S.Lbar ((k : G) * g))) =
      finrank (ZMod 2) (nqSub S g t (S.Lbar g)) := by
    rw [← hmap, LinearEquiv.finrank_map_eq]
  omega

section Rel

variable [NQHyp S g t] {X : Hyp10 S g t} (F : Frame X)
include F

theorem nq_rel_three {r : Rbar S g t} {γ : Gm} (hr : F.π r = γ) (hγ : γ * γ * γ = 1)
    (v : NQ S g t) : nqLin r (nqLin r (nqLin r v)) = v := by
  have hπ : F.π (r * r * r) = F.π 1 := by
    rw [map_one, map_mul, map_mul, hr]
    exact hγ
  rw [nqLin_comp, nqLin_comp, nqLin_eq_of_pi_eq F hπ, nqLin_one]

theorem nq_rel_two {r : Rbar S g t} {γ : Gm} (hr : F.π r = γ) (hγ : γ * γ = 1)
    (v : NQ S g t) : nqLin r (nqLin r v) = v := by
  have hπ : F.π (r * r) = F.π 1 := by
    rw [map_one, map_mul, hr]
    exact hγ
  rw [nqLin_comp, nqLin_eq_of_pi_eq F hπ, nqLin_one]

theorem nq_rel_comm {a b : Rbar S g t} {α β : Gm} (ha : F.π a = α) (hb : F.π b = β)
    (h : α * β = β * α) (v : NQ S g t) : nqLin a (nqLin b v) = nqLin b (nqLin a v) := by
  have hπ : F.π (a * b) = F.π (b * a) := by
    rw [map_mul, map_mul, ha, hb]
    exact h
  rw [nqLin_comp, nqLin_comp, nqLin_eq_of_pi_eq F hπ]

theorem nq_rel_inv {a b : Rbar S g t} {α β : Gm} (ha : F.π a = α) (hb : F.π b = β)
    (h : α * β = β * β * α) (v : NQ S g t) :
    nqLin a (nqLin b v) = nqLin b (nqLin b (nqLin a v)) := by
  have hπ : F.π (a * b) = F.π (b * b * a) := by
    rw [map_mul, map_mul, map_mul, ha, hb]
    exact h
  rw [nqLin_comp, nqLin_comp, nqLin_comp, nqLin_eq_of_pi_eq F hπ]

end Rel

theorem nq_block
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) [NQHyp S g t] (F : Frame X)
    {rd re r₁ r₂ : Rbar S g t} (hd : F.π rd = σ₁) (he : F.π re = σ₂) (h₁ : F.π r₁ = τ₁)
    (h₂ : F.π r₂ = τ₂) (hr₁L : (r₁ : S.O) ∈ S.Lbar g) (hr₂L : (r₂ : S.O) ∈ S.Lbar g) :
    LinearMap.ker (nqLin r₁ - 1) ≤ (LinearMap.ker (nqLin r₁ - 1) ⊓ LinearMap.ker (nqLin r₂ - 1)) ⊔
      (LinearMap.ker (nqLin r₁ - 1) ⊓ LinearMap.ker (nqLin r₂ - 1)).map (nqLin re) := by
  refine block_fix (nqLin rd) (nqLin re) (nqLin r₁) (nqLin r₂) (nq_rel_three F hd σ₁_cube)
    (nq_rel_three F he σ₂_cube) (nq_rel_two F h₁ τ₁_sq) (nq_rel_two F h₂ τ₂_sq)
    (nq_rel_comm F hd he σ₁_σ₂_comm) (nq_rel_comm F h₁ h₂ τ₁_τ₂_comm) (nq_rel_inv F h₁ hd τ₁_σ₁)
    (nq_rel_comm F h₁ he τ₁_σ₂) (nq_rel_comm F h₂ hd τ₂_σ₁) (nq_rel_inv F h₂ he τ₂_σ₂)
    (fun v h1 h2 h3 h4 => eq_zero_of_fix_all hCE X (fix_all_of_fix_gen F hd he h₁ h₂ h1 h2 h3 h4))
    ?_
  have hle : nqSub S g t (S.Lbar g) ≤
      LinearMap.ker (nqLin r₁ - 1) ⊓ LinearMap.ker (nqLin r₂ - 1) := by
    rintro _ ⟨n, hn, rfl⟩
    have hc : ∀ r : Rbar S g t, (r : S.O) ∈ S.Lbar g → nqLin r (nqMk n) = nqMk n := by
      intro r hr
      rw [nqLin_mk, nqMk_nConj_eq_iff, S4.Lbar_comm S X.haQ hr hn, mul_inv_cancel_right,
        mul_inv_cancel]
      exact one_mem _
    exact ⟨LinearMap.mem_ker.mpr (by simp [hc r₁ hr₁L]),
      LinearMap.mem_ker.mpr (by simp [hc r₂ hr₂L])⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_nq_eq hCE X
  omega

theorem comm_mem_ker
    (X : Hyp10 S g t) [NQHyp S g t] (F : Frame X) {k : S.M}
    (hkR : S.ρ k ∈ Rbar S g t) (hπk : F.π ⟨S.ρ k, hkR⟩ = σ₂) {r₁ : Rbar S g t}
    (hπr₁ : F.π r₁ = τ₁) (hr₁L : (r₁ : S.O) ∈ S.Lbar g) :
    ∃ hm : (r₁ : S.O)⁻¹ * (S.ρ k * r₁ * (S.ρ k)⁻¹) ∈ Nbar S g t,
      nqMk ⟨_, hm⟩ ∈ LinearMap.ker (nqLin r₁ - 1) := by
  have hcR : S.ρ k * r₁ * (S.ρ k)⁻¹ ∈ Rbar S g t := mul_mem (mul_mem hkR r₁.2) (inv_mem hkR)
  have hmR : (r₁ : S.O)⁻¹ * (S.ρ k * r₁ * (S.ρ k)⁻¹) ∈ Rbar S g t :=
    mul_mem (inv_mem r₁.2) hcR
  have hmN : (r₁ : S.O)⁻¹ * (S.ρ k * r₁ * (S.ρ k)⁻¹) ∈ Nbar S g t := by
    refine (F.ker ⟨_, hmR⟩).mp ?_
    have e : (⟨_, hmR⟩ : Rbar S g t) =
        r₁⁻¹ * (⟨S.ρ k, hkR⟩ * r₁ * (⟨S.ρ k, hkR⟩ : Rbar S g t)⁻¹) := Subtype.ext (by simp)
    rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hπr₁, hπk]
    exact τ₁_comm_σ₂
  refine ⟨hmN, ?_⟩
  have hcL : S.ρ k * r₁ * (S.ρ k)⁻¹ ∈ S.Lbar ((k : G) * g) := conj_mem_Lbar_mul S k hr₁L
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, nqLin_mk,
    nqMk_nConj_eq_iff]
  have hsq := NQHyp.sq _ hmN
  change (r₁ : S.O) * ((r₁ : S.O)⁻¹ * (S.ρ k * r₁ * (S.ρ k)⁻¹)) * (r₁ : S.O)⁻¹ *
    ((r₁ : S.O)⁻¹ * (S.ρ k * r₁ * (S.ρ k)⁻¹))⁻¹ ∈ zpowers t
  rw [conj_inv_aux (S4.mul_self_of_mem_Lbar S X.haQ hr₁L)
    (S4.mul_self_of_mem_Lbar S (conj_mem_QG' S k.2 X.haQ) hcL)]
  exact inv_mem hsq

theorem exists_Lbar_of_mem_C (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) [NQHyp S g t]
    (F : Frame X) {r₁ r₂ : Rbar S g t} (h₁ : F.π r₁ = τ₁) (h₂ : F.π r₂ = τ₂)
    (hr₁L : (r₁ : S.O) ∈ S.Lbar g) (hr₂L : (r₂ : S.O) ∈ S.Lbar g) {v : NQ S g t}
    (hv : v ∈ LinearMap.ker (nqLin r₁ - 1) ⊓ LinearMap.ker (nqLin r₂ - 1)) :
    ∃ a : Nbar S g t, (a : S.O) ∈ S.Lbar g ∧ nqMk a = v := by
  obtain ⟨n, rfl⟩ := nqMk_surjective v
  have h1 : nqLin r₁ (nqMk n) = nqMk n := by
    have := LinearMap.mem_ker.mp hv.1
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  have h2 : nqLin r₂ (nqMk n) = nqMk n := by
    have := LinearMap.mem_ker.mp hv.2
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  rw [nqLin_mk, nqMk_nConj_eq_iff] at h1 h2
  exact ⟨n, mem_Lbar_of_comm_two hCE X F hr₁L hr₂L h₁ h₂ n.2 h1 h2, rfl⟩

theorem exists_decomp (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) [NQHyp S g t]
    (F : Frame X) {r₁ r₂ : Rbar S g t} (h₁ : F.π r₁ = τ₁) (h₂ : F.π r₂ = τ₂)
    (hr₁L : (r₁ : S.O) ∈ S.Lbar g) (hr₂L : (r₂ : S.O) ∈ S.Lbar g) {k : S.M}
    (hkR : S.ρ k ∈ Rbar S g t) {n : Nbar S g t}
    (hn : (nqMk n : NQ S g t) ∈ ((LinearMap.ker (nqLin r₁ - 1) ⊓ LinearMap.ker (nqLin r₂ - 1)) ⊔
      (LinearMap.ker (nqLin r₁ - 1) ⊓ LinearMap.ker (nqLin r₂ - 1)).map
        (nqLin (⟨S.ρ k, hkR⟩ : Rbar S g t)) : Submodule (ZMod 2) (NQ S g t))) :
    ∃ a ∈ S.Lbar g ⊓ Nbar S g t, ∃ e ∈ S.Lbar ((k : G) * g), (a * e)⁻¹ * n ∈ zpowers t := by
  obtain ⟨c₁, hc₁, w, hw, hsum⟩ := Submodule.mem_sup.mp hn
  obtain ⟨c₂, hc₂, rfl⟩ := hw
  obtain ⟨a, haL, ha⟩ := exists_Lbar_of_mem_C hCE X F h₁ h₂ hr₁L hr₂L hc₁
  obtain ⟨a', ha'L, ha'⟩ := exists_Lbar_of_mem_C hCE X F h₁ h₂ hr₁L hr₂L hc₂
  rw [← ha, ← ha', nqLin_mk, ← nqMk_mul, nqMk_eq_iff] at hsum
  refine ⟨a, Subgroup.mem_inf.mpr ⟨haL, a.2⟩, (nConj (⟨S.ρ k, hkR⟩ : Rbar S g t) a' : Nbar S g t),
    ?_, ?_⟩
  · rw [coe_nConj]
    exact conj_mem_Lbar_mul S k ha'L
  · simpa using hsum

theorem exists_mem_Lbar_inf_conj
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X) :
    ∃ k : S.M, ∃ hk : S.ρ k ∈ Rbar S g t, F.π ⟨S.ρ k, hk⟩ = σ₂ ∧
      ∃ x, ∃ hx : x ∈ S.Lbar g, x ∈ S.Lbar ((k : G) * g) ∧
        F.π ⟨x, Lbar_le_Rbar X.ht hx⟩ = τ₁ := by
  have := X.nqHyp hCE
  obtain ⟨rd, hd⟩ := F.surj σ₁
  obtain ⟨re, he⟩ := F.surj σ₂
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar re.2)
  have hkR : S.ρ k ∈ Rbar S g t := hk ▸ re.2
  have hre : (⟨S.ρ k, hkR⟩ : Rbar S g t) = re := Subtype.ext hk
  have hπk : F.π ⟨S.ρ k, hkR⟩ = σ₂ := by rw [hre, he]
  obtain ⟨x₁, hx₁L, hπx₁⟩ := F.exists_Lbar_of_stab (γ := τ₁)
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inl rfl))
  obtain ⟨y₁, hy₁L, hπy₁⟩ := F.exists_Lbar_of_stab (γ := τ₂)
    (by rw [mem_stabA, act_E00_iff]; exact Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨r₁, hr₁⟩ : ∃ r : Rbar S g t, r = ⟨x₁, Lbar_le_Rbar X.ht hx₁L⟩ := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r : Rbar S g t, r = ⟨y₁, Lbar_le_Rbar X.ht hy₁L⟩ := ⟨_, rfl⟩
  have hπr₁ : F.π r₁ = τ₁ := by rw [hr₁]; exact hπx₁
  have hπr₂ : F.π r₂ = τ₂ := by rw [hr₂]; exact hπy₁
  have hr₁L : (r₁ : S.O) ∈ S.Lbar g := by rw [hr₁]; exact hx₁L
  have hr₂L : (r₂ : S.O) ∈ S.Lbar g := by rw [hr₂]; exact hy₁L
  clear hr₁ hr₂ hπx₁ hπy₁ hx₁L hy₁L x₁ y₁
  have hB := nq_block hCE X F hd he hπr₁ hπr₂ hr₁L hr₂L
  rw [← hre] at hB
  obtain ⟨hmN, hmker⟩ := comm_mem_ker X F hkR hπk hπr₁ hr₁L
  obtain ⟨a, haL, e, heL, hae⟩ := exists_decomp hCE X F hπr₁ hπr₂ hr₁L hr₂L hkR (hB hmker)
  obtain ⟨j, hj⟩ := hae
  have htc : t ∈ S.Lbar ((k : G) * g) := mem_Lbar_mul_of_mem_Rbar X.H X.ht hkR
  have hcL : S.ρ k * r₁ * (S.ρ k)⁻¹ ∈ S.Lbar ((k : G) * g) := conj_mem_Lbar_mul S k hr₁L
  have haN : a ∈ Nbar S g t := haL.2
  replace haL : a ∈ S.Lbar g := haL.1
  refine ⟨k, hkR, hπk, r₁ * a, mul_mem hr₁L haL, ?_, ?_⟩
  · have e1 : (r₁ : S.O) * a = S.ρ k * r₁ * (S.ρ k)⁻¹ * (e * t ^ j)⁻¹ := by
      have hj' : t ^ j = (a * e)⁻¹ * ((r₁ : S.O)⁻¹ * (S.ρ k * r₁ * (S.ρ k)⁻¹)) := hj
      rw [hj']
      group
    rw [e1]
    exact mul_mem hcL (inv_mem (mul_mem heL (zpow_mem htc j)))
  · have haR := Lbar_le_Rbar X.ht haL
    have e : (⟨r₁ * a, Lbar_le_Rbar X.ht (mul_mem hr₁L haL)⟩ : Rbar S g t) =
        r₁ * ⟨a, haR⟩ := Subtype.ext (by simp)
    rw [e, map_mul, hπr₁, (F.ker ⟨a, haR⟩).mpr haN, mul_one]

end CFSG.LargeExtraspecial.S10
