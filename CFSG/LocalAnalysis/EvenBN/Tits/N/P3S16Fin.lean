module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16Orb
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16Str
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S15
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Alt2D

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section Conj

variable {G : Type} [Group G]

@[expose] def SConj (S : Subgroup G) (a b : G) : Prop := ∃ s ∈ S, s * a * s⁻¹ = b

theorem SConj.symm {S : Subgroup G} {a b : G} (h : SConj S a b) : SConj S b a := by
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s⁻¹, inv_mem hs, by group⟩

theorem SConj.trans {S : Subgroup G} {a b c : G} (h₁ : SConj S a b) (h₂ : SConj S b c) :
    SConj S a c := by
  obtain ⟨s, hs, rfl⟩ := h₁
  obtain ⟨s', hs', rfl⟩ := h₂
  exact ⟨s' * s, mul_mem hs' hs, by group⟩

end Conj

section Abs

variable {Γ : Type*} [Group Γ]

theorem isPGroup_sup_zpowers {a b : Γ} (hab : a * b = b * a) {k m : ℕ} (ha : a ^ (2 ^ k) = 1)
    (hb : b ^ (2 ^ m) = 1) : IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup Γ) := by
  have hnorm : zpowers a ≤ normalizer (zpowers b : Set Γ) := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨i, rfl⟩ := hu
    obtain ⟨j, rfl⟩ := hw
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq.symm
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers a) (zpowers b) hnorm
  intro g
  obtain ⟨g, hg⟩ := g
  have hg' : g ∈ ((zpowers a : Set Γ) * (zpowers b : Set Γ)) := by
    rw [← hset]
    exact hg
  obtain ⟨u, hu, w, hw, rfl⟩ := hg'
  have hu1 : u ^ (2 ^ k) = 1 := by
    obtain ⟨i, rfl⟩ := hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hw1 : w ^ (2 ^ m) = 1 := by
    obtain ⟨j, rfl⟩ := hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  have hcomm : Commute u w := by
    obtain ⟨i, rfl⟩ := hu
    obtain ⟨j, rfl⟩ := hw
    exact Commute.zpow_zpow (show Commute a b from hab) i j
  refine ⟨k + m, Subtype.ext ?_⟩
  show (u * w) ^ (2 ^ (k + m)) = 1
  have hu2 : u ^ (2 ^ (k + m)) = 1 := by rw [pow_add, pow_mul, hu1, one_pow]
  have hw2 : w ^ (2 ^ (k + m)) = 1 := by rw [add_comm, pow_add, pow_mul, hw1, one_pow]
  rw [hcomm.mul_pow, hu2, hw2, one_mul]

end Abs

section S16Fin

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem star_y_ne (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) {y₁ : G}
    (hy : IsV1 d z₀ y₁) {θ : MulAut ↥d.s56V} (hθx : θ * star d d.x₅ = star d d.x₅ * θ) :
    θ * star d y₁ * θ⁻¹ ≠ star d y₁ * star d d.t := by
  intro h
  have hyz : star d y₁ (zV h49 hd) = zV h49 hd :=
    (actFun_fixes_iff d.s56V (y1_mem_Hg h49 hd hy) _).2 (hd.s56_M_comm_z (hy.mem_M hd))
  have hyz₀ : star d y₁ (z0V hz) = z0V hz :=
    (actFun_fixes_iff d.s56V (y1_mem_Hg h49 hd hy) _).2 hy.2.1
  have h1 : (θ * star d y₁ * θ⁻¹) (z0V hz) = (star d y₁ * star d d.t) (z0V hz) := by rw [h]
  have hθ'x : θ⁻¹ * star d d.x₅ = star d d.x₅ * θ⁻¹ := by
    calc θ⁻¹ * star d d.x₅ = θ⁻¹ * (star d d.x₅ * θ) * θ⁻¹ := by group
      _ = θ⁻¹ * (θ * star d d.x₅) * θ⁻¹ := by rw [hθx]
      _ = star d d.x₅ * θ⁻¹ := by group
  have hxz₀ : star d d.x₅ (z0V hz) = z0V hz :=
    (star_x5_fix_iff h49 hd hz h10 _).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hfix : star d d.x₅ (θ⁻¹ (z0V hz)) = θ⁻¹ (z0V hz) := by
    have h2 : (θ⁻¹ * star d d.x₅) (z0V hz) = (star d d.x₅ * θ⁻¹) (z0V hz) := by rw [hθ'x]
    rw [MulAut.mul_apply, MulAut.mul_apply, hxz₀] at h2
    exact h2.symm
  have hyfix : star d y₁ (θ⁻¹ (z0V hz)) = θ⁻¹ (z0V hz) := by
    rcases (star_x5_fix_iff h49 hd hz h10 _).1 hfix with h' | h' | h' | h'
    · rw [h', map_one]
    · rw [h', hyz]
    · rw [h', hyz₀]
    · rw [h', map_mul, hyz, hyz₀]
  have h2 : (θ * star d y₁ * θ⁻¹) (z0V hz) = z0V hz := by
    rw [MulAut.mul_apply, MulAut.mul_apply, hyfix]
    simp
  have h3 : (star d y₁ * star d d.t) (z0V hz) = z0V hz * zV h49 hd := by
    rw [MulAut.mul_apply, star_t_z0V h49 hd hz h10, map_mul, hyz₀, hyz]
  rw [h2, h3] at h1
  have h4 : zV h49 hd = 1 := mul_eq_left.1 h1.symm
  exact hd.s56_z_ne_one (congrArg Subtype.val h4)

theorem star_t_comm_transv (h49 : d.Thm49Statement) (hd : d.Hyp) {β : G} (hβH : β ∈ Hg d)
    (hTr : IsTransv β d.s56V d.z (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z)) :
    star d d.t * star d β = star d β * star d d.t := by
  obtain ⟨-, -, -, hall⟩ := hTr
  have htH : d.t ∈ Hg d := t_mem_Hg h49 hd
  have htN : d.t ∈ normalizer (d.s56V : Set G) := htH
  have hβN : β ∈ normalizer (d.s56V : Set G) := hβH
  have hz1 : d.z * d.t = d.t * d.z := hd.L_comm_t d.z_mem
  have hx1 : d.x₅ * d.t = d.t * d.x₅ := hd.s56_x5_comm_t
  have htz : d.t * d.z * d.t⁻¹ = d.z := by
    calc d.t * d.z * d.t⁻¹ = d.z * d.t * d.t⁻¹ := by rw [hz1]
      _ = d.z := by group
  have htX : d.t ∈ normalizer ((Xg d : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun g hg => ?_)
    have hg' : g ∈ zpowers d.x₅ := hg
    obtain ⟨n, rfl⟩ := hg'
    exact (Commute.zpow_left (show Commute d.x₅ d.t from hx1) n).eq
  have htZ : d.t ∈ normalizer ((zpowers d.z : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun g hg => ?_)
    obtain ⟨n, rfl⟩ := hg
    exact (Commute.zpow_left (show Commute d.z d.t from hz1) n).eq
  have htA : d.t ∈ normalizer (((⁅d.s56V, Xg d⁆ ⊔ zpowers d.z : Subgroup G)) : Set G) :=
    P4.mem_normalizer_sup' (P4.mem_normalizer_commutator htN htX) htZ
  have hax : ∀ v : G, v ∈ (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z : Subgroup G) ↔
      d.t * v * d.t⁻¹ ∈ (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z : Subgroup G) :=
    fun v => mem_normalizer_iff.1 htA v
  have hct : ∀ l : ↥d.s56V, ((star d d.t l : ↥d.s56V) : G) = d.t * (l : G) * d.t⁻¹ := fun l => by
    rw [star_eq, actFun_apply_coe d.s56V htN]
  have hcβ : ∀ l : ↥d.s56V, ((star d β l : ↥d.s56V) : G) = β * (l : G) * β⁻¹ := fun l => by
    rw [star_eq, actFun_apply_coe d.s56V hβN]
  refine MulEquiv.ext fun v => Subtype.ext ?_
  show ((star d d.t (star d β v) : ↥d.s56V) : G) = ((star d β (star d d.t v) : ↥d.s56V) : G)
  simp only [hct, hcβ]
  have hv₁ : d.t * (v : G) * d.t⁻¹ ∈ d.s56V := (mem_normalizer_iff.1 htN (v : G)).1 v.2
  obtain ⟨hd₀, hi₀⟩ := hall (v : G) v.2
  obtain ⟨hd₁, hi₁⟩ := hall _ hv₁
  by_cases hv : (v : G) ∈ (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z : Subgroup G)
  · have e₀ : β * (v : G) * β⁻¹ = v := hi₀.2 hv
    have e₁ : β * (d.t * (v : G) * d.t⁻¹) * β⁻¹ = d.t * (v : G) * d.t⁻¹ := hi₁.2 ((hax _).1 hv)
    rw [e₀, e₁]
  · have e₀ : β * (v : G) * β⁻¹ = v * d.z := by
      rcases hd₀ with h | h
      · exact absurd (hi₀.1 h) hv
      · exact h
    have hv' : d.t * (v : G) * d.t⁻¹ ∉ (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z : Subgroup G) :=
      fun h => hv ((hax _).2 h)
    have e₁ : β * (d.t * (v : G) * d.t⁻¹) * β⁻¹ = d.t * (v : G) * d.t⁻¹ * d.z := by
      rcases hd₁ with h | h
      · exact absurd (hi₁.1 h) hv'
      · exact h
    rw [e₀, e₁]
    calc d.t * ((v : G) * d.z) * d.t⁻¹ = d.t * (v : G) * d.t⁻¹ * (d.t * d.z * d.t⁻¹) := by group
      _ = d.t * (v : G) * d.t⁻¹ * d.z := by rw [htz]

theorem node16_b (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h12 : Node12 d z₀) (h15 : Node15 d z₀) (h17s : Node17s d z₀)
    {S : Subgroup G} (hS : fusionIsSylowIn 2 S (Cv d)) (hSt : ∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S)
    (h69 : Cv d = oddCoreSub (Cv d) ⊔ d.s56V ∨
      ({x | ∃ c ∈ Cv d, c * d.t * c⁻¹ = x} ∩ (S ⊔ zpowers d.t : Subgroup G) =
          {x | ∃ s ∈ S, s * d.t * s⁻¹ = x} ∧
        ∃ b : G, (∃ s ∈ S, b = s * d.t) ∧ b * b = 1 ∧ ∀ x : G, (∃ s ∈ S, x = s * d.t) → x * x = 1 →
          (∃ s ∈ S, s * d.t * s⁻¹ = x) ∨ ∃ s ∈ S, s * b * s⁻¹ = x)) :
    ((Trans S (OrbSet d S) ∧
        img d (Hg d ⊓ centralizer ({d.t} : Set G)) = centralizer ({star d d.t} : Set _) ⊓ Hs d) ∨
      ((∃ a ∈ OrbSet d S, ∃ b ∈ OrbSet d S, (∀ x ∈ OrbSet d S, (∃ s ∈ S, s * a * s⁻¹ = x) ∨
          (∃ s ∈ S, s * b * s⁻¹ = x)) ∧ ¬ ∃ s ∈ S, s * a * s⁻¹ = b) ∧
        ∃ β ∈ Hg d, centralizer ({star d d.t} : Set _) ⊓ Hs d = img d (CMt d) ⊔ zpowers (star d β) ∧
          img d (CMt d) ⊓ zpowers (star d β) = ⊥ ∧
          (∀ c ∈ img d (CMt d), c * star d β = star d β * c) ∧
          IsTransv β d.s56V d.z (⁅d.s56V, Xg d⁆ ⊔ zpowers d.z) ∧
          d.s56V ⊓ centralizer ({d.t * β} : Set G) = d.E ⊔ zpowers z₀)) := by
  by_cases hTr : Trans S (OrbSet d S)
  · exact Or.inl ⟨hTr, part_a h49 hd hz hS hSt hTr⟩
  right
  have hSK : S ≤ Cv d := hS.1
  rcases h69 with hK | ⟨hK, b₀, ⟨s₀, hs₀, hb₀⟩, -, hb₀all⟩
  · exact absurd (trans_of_oddCore h49 hd h10 h12 hS hK) hTr
  have hOall : ∀ x ∈ OrbSet d S, SConj S d.t x ∨ SConj S b₀ x := by
    intro x hx
    obtain ⟨hx2, s, hs, hxs⟩ := OrbSet_facts hd hx
    exact hb₀all x ⟨s, hs, hxs⟩ hx2
  obtain ⟨a, ha, a', ha', hna⟩ : ∃ a ∈ OrbSet d S, ∃ a' ∈ OrbSet d S, ¬ SConj S a a' := by
    by_contra hno
    push Not at hno
    exact hTr fun a ha b hb => hno a ha b hb
  have hΩconj : ∀ {u v : G}, u ∈ OrbSet d S → SConj S u v → v ∈ OrbSet d S := by
    rintro u v hu ⟨s, hs, hsv⟩
    rw [← hsv]
    exact OrbSet_conj_mem hSK hSt hu hs
  have key : b₀ ∈ OrbSet d S ∧ ¬ SConj S d.t b₀ := by
    rcases hOall a ha with h1 | h1 <;> rcases hOall a' ha' with h2 | h2
    · exact absurd (h1.symm.trans h2) hna
    · exact ⟨hΩconj ha' h2.symm, fun h => hna (h1.symm.trans (h.trans h2))⟩
    · exact ⟨hΩconj ha h1.symm, fun h => hna (h1.symm.trans (h.symm.trans h2))⟩
    · exact absurd (h1.symm.trans h2) hna
  refine ⟨⟨d.t, t_mem_OrbSet S, b₀, key.1, hOall, key.2⟩, ?_⟩
  obtain ⟨y₁, hy⟩ : ∃ y₁, IsV1 d z₀ y₁ := h09.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hU, hU16, h17⟩ := h17s
  obtain ⟨h17c, h17i, h17t⟩ := h17 y₁ hy
  have hF : P4.IsF20 (Us d) (star d d.x₅) (star d y₁) := P4.isF20_Us h49 hd hz h10 hU hU16 hy
  have hPe := P4.P_eq h49 hd y₁
  rw [hPe] at h17c h17i h17t
  have hΞΘ := img_CMt_le_Th h49 hd
  have hcos : ∀ θ ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d,
      θ ∉ img d (CMt d) → ∀ θ' ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d,
      θ' ∉ img d (CMt d) → θ⁻¹ * θ' ∈ img d (CMt d) :=
    fun θ hθ hθΞ θ' hθ' hθ'Ξ => coset_lemma h49 hd hz hS hSt (b := b₀) hOall hθ hθ' hθΞ hθ'Ξ
  have hnorm : ∀ θ ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d,
      ∀ ξ ∈ img d (CMt d), θ * ξ * θ⁻¹ ∈ img d (CMt d) := by
    intro θ hθ ξ hξ
    by_cases hθΞ : θ ∈ img d (CMt d)
    · exact mul_mem (mul_mem hθΞ hξ) (inv_mem hθΞ)
    · by_contra hno
      have hΘ' : θ * ξ * θ⁻¹ ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d :=
        mul_mem (mul_mem hθ (hΞΘ hξ)) (inv_mem hθ)
      have h1 := hcos θ hθ hθΞ _ hΘ' hno
      have h2 : θ⁻¹ ∈ img d (CMt d) := by
        have e : θ⁻¹ * (θ * ξ * θ⁻¹) = ξ * θ⁻¹ := by group
        rw [e] at h1
        have h3 := mul_mem (inv_mem hξ) h1
        simpa using h3
      exact hθΞ (by simpa using inv_mem h2)
  have hC : S16.Ctx (Us d) (star d d.x₅) (star d y₁) (star d d.t) (img d (CMt d))
      (centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d) :=
    { F := hF, Ξ_eq := h17c, t2 := star_t_mul_self h49 hd, t1 := star_t_ne h49 hd hz,
      tP := fun p hp => h17t p hp, tinf := h17i, ΞΘ := hΞΘ,
      Θt := fun θ hθ => mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hθ).1,
      norm := hnorm, cos := hcos }
  have hK' : (∃ k ∈ Cv d, k * d.t * k⁻¹ = b₀) → ∃ s ∈ S, s * d.t * s⁻¹ = b₀ := by
    intro hk
    have hmem : b₀ ∈ {x | ∃ c ∈ Cv d, c * d.t * c⁻¹ = x} ∩ (S ⊔ zpowers d.t : Subgroup G) :=
      ⟨hk, by rw [hb₀]; exact mul_mem (mem_sup_left hs₀) (mem_sup_right (mem_zpowers d.t))⟩
    rw [hK] at hmem
    exact hmem
  obtain ⟨θ₀, hθ₀, hθ₀Ξ⟩ := exists_mem_Th_not_Xi h49 hd hSK key.1 key.2 hK'
  obtain ⟨β, hβΘ, hβΞ, hβx, k, hβ2⟩ := hC.exists_two_part hθ₀ hθ₀Ξ
  have hβU := hC.centralizes_U hβΘ hβx hβ2
  have hβy : β * star d y₁ = star d y₁ * β := by
    rcases hC.comm_y_or hβΘ hβx hβU with h | h
    · calc β * star d y₁ = (β * star d y₁ * β⁻¹) * β := by group
        _ = star d y₁ * β := by rw [h]
    · exact absurd h (star_y_ne h49 hd hz h10 hy hβx)
  have hβt : β * star d d.t = star d d.t * β := hC.Θt β hβΘ
  have hβc : ∀ ξ ∈ img d (CMt d), ξ * β = β * ξ := hC.comm_Ξ_of_gens hβt hβx hβy hβU
  have htc : star d d.t * star d d.x₅ = star d d.x₅ * star d d.t :=
    actFun_comm_of_comm d.s56V (g := d.t) (h := d.x₅) hd.s56_x5_comm_t.symm
  have hty : star d d.t * star d y₁ = star d y₁ * star d d.t := hC.tP _ hC.y_mem_P
  have hcent : ∀ g : MulAut ↥d.s56V, g * star d d.x₅ = star d d.x₅ * g →
      g * star d y₁ = star d y₁ * g →
      g ∈ centralizer ((img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) :
        Set (MulAut ↥d.s56V)) := by
    intro g hgx hgy
    have hle : (img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) ≤
        centralizer ({g} : Set (MulAut ↥d.s56V)) :=
      sup_le (by
          rw [P4.img_Xg h49 hd]
          exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hgx.symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hgy.symm))
    exact mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hle hh)
  have hB2 : IsPGroup 2 (zpowers (star d d.t) ⊔ zpowers β : Subgroup (MulAut ↥d.s56V)) :=
    isPGroup_sup_zpowers (a := star d d.t) (b := β) hβt.symm (k := 1) (m := k)
      (by rw [pow_one, pow_two]; exact hC.t2) hβ2
  have hBC : (zpowers (star d d.t) ⊔ zpowers β : Subgroup (MulAut ↥d.s56V)) ≤
      centralizer ((img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) :
        Set (MulAut ↥d.s56V)) ⊓ Hs d :=
    sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨hcent _ htc hty,
        actFun_mem_imgIn (t_mem_Hg h49 hd) (t_mem_Hg h49 hd)⟩))
      (zpowers_le.2 (Subgroup.mem_inf.2 ⟨hcent β hβx hβy, (Subgroup.mem_inf.1 hβΘ).2⟩))
  obtain ⟨S', hBS', hS'⟩ := S16.exists_fusionIsSylowIn' hB2 hBC
  have hts' : star d d.t ∈ S' := hBS' (mem_sup_left (mem_zpowers _))
  have hβS' : β ∈ S' := hBS' (mem_sup_right (mem_zpowers _))
  rcases h15 y₁ hy S' hS' hts' with hS'eq | ⟨β', hβ'H, hS'cl, hTrv, hCV⟩
  · exfalso
    rw [hS'eq] at hβS'
    rcases eq_one_or_of_mem_zpowers hC.t2 hβS' with h | h
    · exact hβΞ (by rw [h]; exact one_mem _)
    · exact hβΞ (by rw [h]; exact hC.t_mem_Ξ)
  · have hτ2 : star d β' * star d β' = 1 := (P4.transv_facts h49 hd h10 hβ'H hTrv).1
    have hτt : star d d.t * star d β' = star d β' * star d d.t :=
      star_t_comm_transv h49 hd hβ'H hTrv
    have hβcl : β ∈ Subgroup.closure ({star d d.t, star d β'} : Set (MulAut ↥d.s56V)) := by
      rw [← hS'cl]
      exact hβS'
    have hcl : Subgroup.closure ({star d d.t, star d β'} : Set (MulAut ↥d.s56V)) ≤
        zpowers (star d d.t) ⊔ zpowers (star d β') := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact mem_sup_left (mem_zpowers _)
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact mem_sup_right (mem_zpowers _)
    have hmem := (mem_sup_zpowers_iff hC.t2 hτ2 hτt β).1 (hcl hβcl)
    obtain ⟨hτΘ, hτΞ, hτc⟩ : star d β' ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d ∧
        star d β' ∉ img d (CMt d) ∧ ∀ c ∈ img d (CMt d), c * star d β' = star d β' * c := by
      rcases hmem with h | h | h | h
      · exact absurd (by rw [h]; exact one_mem _) hβΞ
      · exact absurd (by rw [h]; exact hC.t_mem_Ξ) hβΞ
      · refine ⟨by rw [← h]; exact hβΘ, by rw [← h]; exact hβΞ, fun c hc => by rw [← h]; exact hβc c hc⟩
      · have hτ : star d β' = star d d.t * β := by rw [h, ← mul_assoc, hC.t2, one_mul]
        refine ⟨?_, ?_, ?_⟩
        · rw [hτ]
          exact mul_mem (hΞΘ hC.t_mem_Ξ) hβΘ
        · rw [hτ]
          intro hm
          apply hβΞ
          have h3 := mul_mem hC.t_mem_Ξ hm
          rwa [← mul_assoc, hC.t2, one_mul] at h3
        · intro c hc
          rw [hτ]
          calc c * (star d d.t * β) = (c * star d d.t) * β := by group
            _ = (star d d.t * c) * β := by rw [← hC.t_comm_Ξ hc]
            _ = star d d.t * (c * β) := by group
            _ = star d d.t * (β * c) := by rw [hβc c hc]
            _ = (star d d.t * β) * c := by group
    refine ⟨β', hβ'H, ?_, ?_, hτc, hTrv, hCV⟩
    · apply le_antisymm
      · intro θ hθ
        by_cases hθΞ : θ ∈ img d (CMt d)
        · exact mem_sup_left hθΞ
        · have h1 := hcos _ hτΘ hτΞ θ hθ hθΞ
          have e : θ = star d β' * ((star d β')⁻¹ * θ) := by group
          rw [e]
          exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left h1)
      · exact sup_le hΞΘ (zpowers_le.2 hτΘ)
    · rw [eq_bot_iff]
      intro g hg
      obtain ⟨hgΞ, hgτ⟩ := Subgroup.mem_inf.1 hg
      rcases eq_one_or_of_mem_zpowers hτ2 hgτ with h | h
      · rw [h]
        exact one_mem _
      · exact absurd (by rw [← h]; exact hgΞ) hτΞ

end S16Fin

end CFSG.LocalAnalysis.EvenBN.Tits.N
