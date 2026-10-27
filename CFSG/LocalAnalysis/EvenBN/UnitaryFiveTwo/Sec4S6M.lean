module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6ModE
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6LMod
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S1C
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] [Finite G] {d : Data G}

@[expose] def commModSub {G : Type*} [Group G] (K M : Subgroup G) : Subgroup G where
  carrier := {s | s ∈ normalizer (K : Set G) ∧ ∀ m ∈ M, m⁻¹ * s * m * s⁻¹ ∈ K}
  one_mem' := ⟨one_mem _, fun m _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨mul_mem haN hbN, fun m hm => ?_⟩
    have e : m⁻¹ * (a * b) * m * (a * b)⁻¹ =
        (m⁻¹ * a * m * a⁻¹) * (a * (m⁻¹ * b * m * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact mul_mem (ha m hm) ((mem_normalizer_iff.1 haN _).1 (hb m hm))
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨inv_mem haN, fun m hm => ?_⟩
    rw [show m⁻¹ * a⁻¹ * m * a⁻¹⁻¹ = (a⁻¹ * (m⁻¹ * a * m * a⁻¹) * a)⁻¹ by group]
    have h1 := (mem_normalizer_iff.1 (inv_mem haN) _).1 (ha m hm)
    rw [inv_inv] at h1
    exact inv_mem h1

theorem mem_normalizer_inf' {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro y
  have h1 := hA y
  have h2 := hB y
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
  exact and_congr h1 h2

theorem X₂sub_le_K₃sub' : X₂sub ≤ K₃sub := X₂sub_le_K₂sub.trans K₂sub_le_K₃sub

theorem X₃sub_le_K₃sub' : X₃sub ≤ K₃sub :=
  le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_right (a := ZX₁sub ⊔ X₂sub))))

theorem ZX₄sub_le_K₃sub' : ZX₄sub ≤ K₃sub :=
  le_sup_of_le_left (le_sup_of_le_left (le_sup_right (a := ZX₁sub ⊔ X₂sub ⊔ X₃sub)))

theorem sup_X₂_X₃_ZX₄_le_K₃sub : X₂sub ⊔ X₃sub ⊔ ZX₄sub ≤ K₃sub :=
  sup_le (sup_le X₂sub_le_K₃sub' X₃sub_le_K₃sub') ZX₄sub_le_K₃sub'

theorem Data.e₁_comm_e₂ (d : Data G) : d.e₁ * d.e₂ = d.e₂ * d.e₁ := by
  show d.ι e₁SU * d.ι e₂SU = d.ι e₂SU * d.ι e₁SU
  rw [← map_mul, ← map_mul, e₁SU_mul_e₂SU]

theorem Data.orderOf_e₁ (d : Data G) : orderOf d.e₁ = 3 := by
  show orderOf (d.ι e₁SU) = 3
  rw [orderOf_injective d.ι d.ι_injective, orderOf_e₁SU]

theorem Data.e₁_mem_sup (d : Data G) : d.e₁ ∈ zpowers d.e₂ ⊔ d.K₃ :=
  Data.Lev_le_zpowers_sup_K₃ d ⟨e₁SU, e₁SU_mem_levHom_range, rfl⟩

section MK

variable (h : d.Hyp)

include h in
theorem Data.Hyp.e₁_mem_NHA₁ : d.e₁ ∈ normalizer (d.A₁ : Set G) ⊓ d.H :=
  Subgroup.mem_inf.2 ⟨Data.Hyp.ι_mem_normalizer_pull e₁SU_mem_normalizer_A₁sub,
    h.L_le_H (d.ι_mem _)⟩

include h in
theorem Data.Hyp.e₁_mem_XW : d.e₁ ∈ d.XW := by
  rw [h.sec4_11_1.1]
  exact mem_sup_left h.e₁_mem_NHA₁

include h in
theorem Data.Hyp.e₁_conj_mem_D₁ {u : G} (hu : u ∈ d.D₁) : d.e₁ * u * d.e₁⁻¹ ∈ d.D₁ :=
  h.conj_mem_D₁ h.e₁_mem_XW hu

include h in
theorem Data.Hyp.e₁_conj_mem_W {w : G} (hw : w ∈ d.W) : d.e₁ * w * d.e₁⁻¹ ∈ d.W := by
  have h1 : d.e₁ ∈ normalizer ((d.withT d.W : Subgroup G) : Set G) := by
    rw [h.sec4_9.2.2.1]
    exact mem_sup_left h.e₁_mem_NHA₁
  exact (mem_normalizer_iff.1 (h.sec4_9.2.2.2.1 h1) w).1 hw

include h in
theorem Data.Hyp.mem_AW_of_comm_e₁ {c : G} (hc : c ∈ d.D₁) (he : d.e₁ * c = c * d.e₁) :
    c ∈ d.A₁ ⊔ d.W := by
  have hθ : c * d.t * c⁻¹ * d.t ∈ d.A₁ ⊔ d.W := h.sec4_11_2.1 c hc
  have hcomAW : ∀ a ∈ d.A₁, ∀ w ∈ d.W, a * w = w * a := fun a ha w hw =>
    mem_centralizer_iff.1 (d.W_le_centralizer hw) a (d.A₁_le_S ha)
  obtain ⟨a, ha, w, hw, hθaw⟩ := KProd.exists_mul_of_mem_sup_of_comm hcomAW hθ
  have heq := h.sec4_11_2.2.2.2.2.1 d.e₁ h.e₁_mem_NHA₁ c
  have hcc : d.e₁ * c * d.e₁⁻¹ = c := by rw [he]; group
  rw [hcc, hθaw] at heq
  have ha' : d.e₁ * a * d.e₁⁻¹ ∈ d.A₁ := (mem_normalizer_iff.1 h.e₁_mem_NHA₁.1 a).1 ha
  have hw' : d.e₁ * w * d.e₁⁻¹ ∈ d.W := h.e₁_conj_mem_W hw
  have hprod : a * w = (d.e₁ * a * d.e₁⁻¹) * (d.e₁ * w * d.e₁⁻¹) := by
    rw [heq]
    group
  have hrel : a⁻¹ * (d.e₁ * a * d.e₁⁻¹) = w * (d.e₁ * w * d.e₁⁻¹)⁻¹ := by
    calc a⁻¹ * (d.e₁ * a * d.e₁⁻¹)
        = a⁻¹ * ((d.e₁ * a * d.e₁⁻¹) * (d.e₁ * w * d.e₁⁻¹)) * (d.e₁ * w * d.e₁⁻¹)⁻¹ := by group
      _ = a⁻¹ * (a * w) * (d.e₁ * w * d.e₁⁻¹)⁻¹ := by rw [hprod]
      _ = w * (d.e₁ * w * d.e₁⁻¹)⁻¹ := by group
  have hζA : a⁻¹ * (d.e₁ * a * d.e₁⁻¹) ∈ d.A₁ := d.A₁.mul_mem (d.A₁.inv_mem ha) ha'
  have hζW : a⁻¹ * (d.e₁ * a * d.e₁⁻¹) ∈ d.W := by
    rw [hrel]
    exact d.W.mul_mem hw (d.W.inv_mem hw')
  have hζH : a⁻¹ * (d.e₁ * a * d.e₁⁻¹) ∈ d.H := h.L_le_H (d.pull_le_L _ hζA)
  have hζZ : a⁻¹ * (d.e₁ * a * d.e₁⁻¹) ∈ d.ZX₄ := by
    rw [← h.sec4_9.2.2.2.2.1]
    exact ⟨hζW, hζH⟩
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨ζ', hζ', hζeq⟩ := hζZ
  have hmodel : e₁SU * α * e₁SU⁻¹ = α * ζ' := by
    apply d.ι_injective
    rw [map_mul, map_mul, map_inv, map_mul, hζeq]
    show d.ι e₁SU * d.ι α * (d.ι e₁SU)⁻¹ =
      d.ι α * ((d.ι α)⁻¹ * (d.ι e₁SU * d.ι α * (d.ι e₁SU)⁻¹))
    group
  have hαZ : α ∈ ZX₄sub := mem_ZX₄sub_of_conj_e₁ hα hζ' hmodel
  have haW : d.ι α ∈ d.W := h.ZX₄_le_W ⟨α, hαZ, rfl⟩
  have hθW : (d.ι α) * w ∈ d.W := d.W.mul_mem haW hw
  have hθW' : c * d.t * c⁻¹ * d.t ∈ d.W := by rw [hθaw]; exact hθW
  exact (h.sec4_11_2.2.2.1 c hc).1 hθW'

include h in
theorem Data.Hyp.mem_K_of_comm_e₂ {c : G} (hcAW : c ∈ d.A₁ ⊔ d.W)
    (he : d.e₂ * c = c * d.e₂) (hYK : d.Y ≤ d.K) (hK₃ : d.K₃ ≤ d.K) : c ∈ d.K := by
  have hcomAW : ∀ a ∈ d.A₁, ∀ w ∈ d.W, a * w = w * a := fun a ha w hw =>
    mem_centralizer_iff.1 (d.W_le_centralizer hw) a (d.A₁_le_S ha)
  obtain ⟨a, ha, w, hw, rfl⟩ := KProd.exists_mul_of_mem_sup_of_comm hcomAW hcAW
  have hwe : w * d.e₂ = d.e₂ * w := h.Y_comm_e₂ (d.W_le_Y hw)
  have hae : d.e₂ * a = a * d.e₂ := by
    have h1 : d.e₂ * (a * w) = (a * w) * d.e₂ := he
    calc d.e₂ * a = d.e₂ * (a * w) * w⁻¹ := by group
      _ = (a * w) * d.e₂ * w⁻¹ := by rw [h1]
      _ = a * (w * d.e₂) * w⁻¹ := by group
      _ = a * (d.e₂ * w) * w⁻¹ := by rw [hwe]
      _ = a * d.e₂ := by group
  obtain ⟨α, hα, rfl⟩ := ha
  have hmodel : e₂SU * α * e₂SU⁻¹ = α := by
    apply d.ι_injective
    rw [map_mul, map_mul, map_inv]
    show d.e₂ * d.ι α * d.e₂⁻¹ = d.ι α
    rw [hae]
    group
  have hsup := mem_sup_of_conj_e₂ hα hmodel
  have haK : d.ι α ∈ d.K := hK₃ (d.pull_mono sup_X₂_X₃_ZX₄_le_K₃sub ⟨α, hsup, rfl⟩)
  exact d.K.mul_mem haK (hYK (d.W_le_Y hw))

include h in
theorem Data.Hyp.M_le_K (hYK : d.Y ≤ d.K) (hK₃ : d.K₃ ≤ d.K) :
    d.D₁ ⊓ centralizer ({d.e₂} : Set G) ≤ d.K := by
  set M : Subgroup G := d.D₁ ⊓ centralizer ({d.e₂} : Set G) with hM
  have hMC : ∀ m ∈ M, m * d.e₂ = d.e₂ * m := fun m hm => mem_centralizer_singleton_iff.1 hm.2
  have hMK : ∀ m ∈ M, m ∈ normalizer (d.K : Set G) := fun m hm =>
    d.mem_normalizer_K (le_normalizer hm.2)
  have he₂ : d.e₂ ∈ commModSub d.K M := by
    refine ⟨d.mem_normalizer_K (le_normalizer (mem_centralizer_singleton_iff.2 rfl)),
      fun m hm => ?_⟩
    have : m⁻¹ * d.e₂ * m * d.e₂⁻¹ = 1 := by
      rw [mul_assoc m⁻¹, ← hMC m hm]
      group
    rw [this]
    exact one_mem _
  have hK₃' : d.K₃ ≤ commModSub d.K M := fun k hk =>
    ⟨le_normalizer (hK₃ hk), fun m hm => by
      have h1 : m⁻¹ * k * m ∈ d.K := by
        have := (mem_normalizer_iff.1 (inv_mem (hMK m hm)) k).1 (hK₃ hk)
        simpa using this
      exact d.K.mul_mem h1 (d.K.inv_mem (hK₃ hk))⟩
  have he₁ : d.e₁ ∈ commModSub d.K M := by
    have : zpowers d.e₂ ⊔ d.K₃ ≤ commModSub d.K M := sup_le (zpowers_le.2 he₂) hK₃'
    exact this (Data.e₁_mem_sup d)
  have hS : zpowers d.e₁ ≤ commModSub d.K M := zpowers_le.2 he₁
  have he₁C : d.e₁ ∈ centralizer ({d.e₂} : Set G) :=
    mem_centralizer_singleton_iff.2 (Data.e₁_comm_e₂ d)
  have he₁M : d.e₁ ∈ normalizer (M : Set G) := mem_normalizer_fintype fun y hy => by
    have hy' : y ∈ M := hy
    refine Subgroup.mem_inf.2 ⟨h.e₁_conj_mem_D₁ (Subgroup.mem_inf.1 hy').1, ?_⟩
    exact (centralizer ({d.e₂} : Set G)).mul_mem
      ((centralizer ({d.e₂} : Set G)).mul_mem he₁C (Subgroup.mem_inf.1 hy').2)
      ((centralizer ({d.e₂} : Set G)).inv_mem he₁C)
  have hSM : zpowers d.e₁ ≤ normalizer (M : Set G) := zpowers_le.2 he₁M
  have hSN : zpowers d.e₁ ≤ normalizer ((M ⊓ d.K : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_inf' (hSM hs) (hS hs).1
  have hMN : M ≤ normalizer ((M ⊓ d.K : Subgroup G) : Set G) := fun m hm =>
    mem_normalizer_inf' (le_normalizer hm) (hMK m hm)
  have hMcard : Nat.card M ∣ 2 ^ 14 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : M ≤ d.D₁)
    rwa [h.card_D₁] at this
  have hsolv : Group.IsSolvable M := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hMcard
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 M := IsPGroup.of_card hi
    haveI := hp.isNilpotent
    infer_instance
  have hcop : (Nat.card (zpowers d.e₁)).Coprime (Nat.card M) := by
    rw [Nat.card_zpowers, d.orderOf_e₁]
    exact Nat.Coprime.coprime_dvd_right hMcard (by norm_num)
  intro m hm
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := M) (N := M ⊓ d.K) (S := zpowers d.e₁) inf_le_left hMN hSM hSN hsolv hcop hm
    (fun s hs => ⟨M.mul_mem (M.inv_mem hm) ((mem_normalizer_iff.1 (hSM hs) m).1 hm),
      by simpa [mul_assoc] using (hS hs).2 m hm⟩)
  have hce : d.e₁ * c = c * d.e₁ := mem_centralizer_iff.1 hc.2 d.e₁ (mem_zpowers d.e₁)
  have hcAW : c ∈ d.A₁ ⊔ d.W := h.mem_AW_of_comm_e₁ hc.1.1 hce
  have hcK : c ∈ d.K := h.mem_K_of_comm_e₂ hcAW (hMC c hc.1).symm hYK hK₃
  exact d.K.mul_mem hcK hn.2

end MK

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
