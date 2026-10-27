module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndBt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

@[expose] def alphaTau {τ : G} (hτ : τ ∈ Bp A t) : ↥D →* ↥Aa :=
  MonoidHom.mk' (fun d => ⟨τ * d * τ⁻¹ * d⁻¹, hD.BpC τ hτ d (hD.le_C d.2)⟩) (fun d d' => by
    apply Subtype.ext
    have hy : τ * (d' : G) * τ⁻¹ * (d' : G)⁻¹ ∈ D :=
      hD.Aa_le (hD.BpC τ hτ d' (hD.le_C d'.2))
    have hyd : (τ * (d' : G) * τ⁻¹ * (d' : G)⁻¹) * (d : G)⁻¹ =
        (d : G)⁻¹ * (τ * (d' : G) * τ⁻¹ * (d' : G)⁻¹) :=
      (show Commute (τ * (d' : G) * τ⁻¹ * (d' : G)⁻¹) (d : G) from
        hD.comm _ hy _ d.2).inv_right.eq
    show τ * ((d : G) * d') * τ⁻¹ * ((d : G) * d')⁻¹ =
      (τ * (d : G) * τ⁻¹ * (d : G)⁻¹) * (τ * (d' : G) * τ⁻¹ * (d' : G)⁻¹)
    calc τ * ((d : G) * d') * τ⁻¹ * ((d : G) * d')⁻¹
        = τ * (d : G) * τ⁻¹ * ((τ * (d' : G) * τ⁻¹ * (d' : G)⁻¹) * (d : G)⁻¹) := by group
      _ = τ * (d : G) * τ⁻¹ * ((d : G)⁻¹ * (τ * (d' : G) * τ⁻¹ * (d' : G)⁻¹)) := by rw [hyd]
      _ = _ := by group)

theorem ThCyc.ker_alphaTau {τ : G} (hτ : τ ∈ Bp A t) :
    (alphaTau hD hτ).ker = (D ⊓ centralizer ({τ} : Set G)).subgroupOf D := by
  ext d
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    have h1 : τ * (d : G) * τ⁻¹ * (d : G)⁻¹ = 1 := congrArg (fun x : ↥Aa => (x : G)) h
    refine ⟨d.2, mem_centralizer_singleton_iff.2 ?_⟩
    have h2 : τ * (d : G) = (d : G) * τ := by
      calc τ * (d : G) = (τ * (d : G) * τ⁻¹ * (d : G)⁻¹) * ((d : G) * τ) := by group
        _ = (d : G) * τ := by rw [h1, one_mul]
    exact h2.symm
  · intro h
    apply Subtype.ext
    have h1 : (d : G) * τ = τ * (d : G) := mem_centralizer_singleton_iff.1 h.2
    show τ * (d : G) * τ⁻¹ * (d : G)⁻¹ = 1
    rw [← h1]
    group

theorem ThCyc.D_alphaTau_mem_A {τ : G} (hτ : τ ∈ Bp A t)
    (hA : ∀ a ∈ A, ∃ x ∈ Aa, τ * x * τ⁻¹ * x⁻¹ = a)
    (hcard : Nat.card ↥(D ⊓ centralizer ({τ} : Set G)) = 2 ^ 8) {d : G} (hd : d ∈ D) :
    τ * d * τ⁻¹ * d⁻¹ ∈ A := by
  set α := alphaTau hD hτ with hα
  have h1 := Subgroup.card_ker_mul_card_range α
  rw [hα, H.ker_alphaTau W W2 hD hτ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      D ⊓ centralizer ({τ} : Set G) ≤ D)).toEquiv, hcard, hD.card] at h1
  have hrange : Nat.card α.range = 16 := by
    have : 2 ^ 8 * Nat.card α.range = 2 ^ 12 := h1
    omega
  have hAle : A.subgroupOf Aa ≤ α.range := by
    intro a ha
    rw [mem_subgroupOf] at ha
    obtain ⟨x, hx, hxa⟩ := hA a ha
    exact ⟨⟨x, hD.Aa_le hx⟩, Subtype.ext hxa⟩
  have hAcard : Nat.card (A.subgroupOf Aa) = 16 := by
    rw [← W.A_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe W2.A_le).toEquiv
  have heq : A.subgroupOf Aa = α.range :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hAcard, hrange])
  have : α ⟨d, hd⟩ ∈ A.subgroupOf Aa := by rw [heq]; exact ⟨_, rfl⟩
  exact mem_subgroupOf.1 this

theorem ThCyc.exists_comm_b {a : G} (ha : a ∈ A) : ∃ x ∈ Aa, b * x * b⁻¹ * x⁻¹ = a := by
  obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 ha
  refine ⟨x, hx, ?_⟩
  have h2 : a * a = 1 := by rw [← sq]; exact W.A_sq _ ha
  rw [W2.b_inv x hx]
  calc x⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by group
    _ = a⁻¹ := by rw [hxa]
    _ = a := inv_eq_of_mul_eq_one_right h2

theorem ThCyc.exists_comm_bt {a : G} (ha : a ∈ A) :
    ∃ x ∈ Aa, (b * t) * x * (b * t)⁻¹ * x⁻¹ = a := by
  obtain ⟨x, hx, hxa⟩ := H.exists_comm_b W W2 hD ha
  refine ⟨x, hx, ?_⟩
  have hxt : t * x = x * t := H.comm_of_mem_L (W.B_le (W2.Aa_le hx))
  rw [← hxa]
  calc (b * t) * x * (b * t)⁻¹ * x⁻¹ = b * (t * x * t⁻¹) * b⁻¹ * x⁻¹ := by group
    _ = b * (x * t * t⁻¹) * b⁻¹ * x⁻¹ := by rw [hxt]
    _ = b * x * b⁻¹ * x⁻¹ := by group

theorem ThCyc.comm_D_mul {τ d₁ d : G} (hτ : τ ∈ Bp A t) (hd₁ : d₁ ∈ D) (hd : d ∈ D) :
    (d₁ * τ) * d * (d₁ * τ)⁻¹ * d⁻¹ = τ * d * τ⁻¹ * d⁻¹ := by
  have h1 : τ * d * τ⁻¹ ∈ D := hD.norm τ hτ.2 d hd
  have h2 : d₁ * (τ * d * τ⁻¹) = (τ * d * τ⁻¹) * d₁ := hD.comm _ hd₁ _ h1
  calc (d₁ * τ) * d * (d₁ * τ)⁻¹ * d⁻¹ = (d₁ * (τ * d * τ⁻¹)) * d₁⁻¹ * d⁻¹ := by group
    _ = ((τ * d * τ⁻¹) * d₁) * d₁⁻¹ * d⁻¹ := by rw [h2]
    _ = τ * d * τ⁻¹ * d⁻¹ := by group

theorem ThCyc.blk_extremal
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B) {g : G}
    (hR : 2 * Nat.card S ≤ Nat.card ↥((S ⊔ Bp A t) ⊓ centralizer ({g⁻¹ * t * g} : Set G)))
    (huP : g⁻¹ * t * g ∈ S ⊔ Bp A t) :
    ∀ x ∈ S ⊔ Bp A t, (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ * x⁻¹ ∈ A := by
  obtain ⟨-, hcard, hPeq, -, d₁, hd₁, hu⟩ := H.ext_extremal_of_card W W2 hD hAb hZ
    (H.isPGroup_S_sup_Bp W)
    (sup_le le_sup_left (zpowers_le.2 (mem_sup_right (H.t_mem_Bp W W2)))) le_sup_right
    (H.S_sup_Bp_le_normalizer W) hR huP
  set u := g⁻¹ * t * g with hu_def
  have hd₁Bp := H.D_le_Bp W W2 hD hd₁
  have hΦ : ∀ d ∈ D, u * d * u⁻¹ * d⁻¹ ∈ A := by
    intro d hd
    rcases hu with h | h | h
    · rw [h, H.comm_D_mul W W2 hD (H.t_mem_Bp W W2) hd₁ hd, H.t_conj_D W W2 hD hd]
      have : theta t d * d * d⁻¹ = theta t d := by group
      rw [this]
      exact H.theta_mem_A W (H.D_le_Bp W W2 hD hd)
    · rw [h, H.comm_D_mul W W2 hD (H.b_mem_Bp W W2) hd₁ hd]
      rw [h, inf_centralizer_mul_eq hD.comm hd₁] at hcard
      exact H.D_alphaTau_mem_A W W2 hD (H.b_mem_Bp W W2) (fun a ha => H.exists_comm_b W W2 hD ha)
        hcard hd
    · have hbt : b * t ∈ Bp A t := mul_mem (H.b_mem_Bp W W2) (H.t_mem_Bp W W2)
      rw [h, H.comm_D_mul W W2 hD hbt hd₁ hd]
      rw [h, inf_centralizer_mul_eq hD.comm hd₁] at hcard
      exact H.D_alphaTau_mem_A W W2 hD hbt (fun a ha => H.exists_comm_bt W W2 hD ha) hcard hd
  intro x hx
  have hRnorm : (S ⊔ Bp A t) ⊓ centralizer ({u} : Set G) ≤ normalizer (D : Set G) :=
    inf_le_left.trans ((H.S_sup_Bp_le_normalizer W).trans (le_normalizer_of_conj_mem hD.norm))
  have hx' : x ∈ D ⊔ (S ⊔ Bp A t) ⊓ centralizer ({u} : Set G) := by
    rw [sup_comm, ← hPeq]
    exact hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D _ hRnorm] at hx'
  obtain ⟨d, hd, r, hr, rfl⟩ := hx'
  have hur : r * u = u * r := mem_centralizer_singleton_iff.1 hr.2
  have h1 : r * u⁻¹ * r⁻¹ = u⁻¹ := by
    calc r * u⁻¹ * r⁻¹ = (r * u * r⁻¹)⁻¹ := by group
      _ = u⁻¹ := by rw [hur]; group
  have e : u * (d * r) * u⁻¹ * (d * r)⁻¹ = u * d * u⁻¹ * d⁻¹ := by
    calc u * (d * r) * u⁻¹ * (d * r)⁻¹ = u * d * (r * u⁻¹ * r⁻¹) * d⁻¹ := by group
      _ = u * d * u⁻¹ * d⁻¹ := by rw [h1]
  rw [e]
  exact hΦ d hd

theorem ThCyc.bt_conj_D (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {d : G} (hd : d ∈ D) :
    (b * t) * d * (b * t)⁻¹ = theta t d * d⁻¹ := by
  calc (b * t) * d * (b * t)⁻¹ = b * (t * d * t⁻¹) * b⁻¹ := by group
    _ = b * (theta t d * d) * b⁻¹ := by rw [H.t_conj_D W W2 hD hd]
    _ = (b * theta t d * b⁻¹) * (b * d * b⁻¹) := by group
    _ = theta t d * d⁻¹ := by rw [H.b_conj_theta W W2 hD hd, hb d hd]

theorem ThCyc.blk_cons_t {g d₁ : G} (hd₁ : d₁ ∈ D) (hu : g⁻¹ * t * g = d₁ * t)
    (hBLK : ∀ x ∈ S ⊔ Bp A t, (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ * x⁻¹ ∈ A) :
    d₁ ^ 2 = theta t d₁ ∧ ∀ s ∈ S, d₁ * s * d₁⁻¹ * s⁻¹ ∈ A := by
  have hd₁Bp := H.D_le_Bp W W2 hD hd₁
  have hθA : theta t d₁ ∈ A := H.theta_mem_A W hd₁Bp
  have hθ2 : theta t d₁ * theta t d₁ = 1 := by rw [← sq]; exact W.A_sq _ hθA
  have hcomm : theta t d₁ * d₁ = d₁ * theta t d₁ := mem_centralizer_iff.1 hd₁Bp.1 _ hθA
  refine ⟨?_, fun s hs => ?_⟩
  · have hu2 := H.conj_sq g
    rw [hu] at hu2
    have h1 : (d₁ * t) ^ 2 = d₁ * (t * d₁ * t⁻¹) * t ^ 2 := by
      simp only [sq]
      group
    rw [h1, H.t_conj_D W W2 hD hd₁, H.sq_t, mul_one] at hu2
    have h2 : theta t d₁ * d₁ ^ 2 = 1 := by
      calc theta t d₁ * d₁ ^ 2 = (theta t d₁ * d₁) * d₁ := by rw [sq]; group
        _ = (d₁ * theta t d₁) * d₁ := by rw [hcomm]
        _ = d₁ * (theta t d₁ * d₁) := by group
        _ = 1 := hu2
    calc d₁ ^ 2 = (theta t d₁)⁻¹ * (theta t d₁ * d₁ ^ 2) := by group
      _ = (theta t d₁)⁻¹ := by rw [h2, mul_one]
      _ = theta t d₁ := inv_eq_of_mul_eq_one_right hθ2
  · have h := hBLK s (mem_sup_left hs)
    rw [hu] at h
    have hts : t * s = s * t := H.comm_of_mem_L (W.S_le hs)
    have e : (d₁ * t) * s * (d₁ * t)⁻¹ * s⁻¹ = d₁ * (t * s * t⁻¹) * d₁⁻¹ * s⁻¹ := by group
    rw [e, show t * s * t⁻¹ = s by rw [hts]; group] at h
    exact h

theorem ThCyc.blk_cons_bt (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {g d₁ : G} (hd₁ : d₁ ∈ D)
    (hu : g⁻¹ * t * g = d₁ * (b * t))
    (hBLK : ∀ x ∈ S ⊔ Bp A t, (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ * x⁻¹ ∈ A) :
    d₁ ∈ Aa ∧ ∀ s ∈ S, (d₁ * b) * s * (d₁ * b)⁻¹ * s⁻¹ ∈ A := by
  have hd₁Bp := H.D_le_Bp W W2 hD hd₁
  have hθA : theta t d₁ ∈ A := H.theta_mem_A W hd₁Bp
  have hcomm : theta t d₁ * d₁ = d₁ * theta t d₁ := mem_centralizer_iff.1 hd₁Bp.1 _ hθA
  refine ⟨?_, fun s hs => ?_⟩
  · have hu2 := H.conj_sq g
    rw [hu] at hu2
    have htb : t * b = b * t := H.comm_of_mem_L (W.B_le W2.b_mem)
    have hbt2 : (b * t) ^ 2 = 1 := by
      calc (b * t) ^ 2 = b * (t * b) * t := by simp only [sq]; group
        _ = b * (b * t) * t := by rw [htb]
        _ = b ^ 2 * t ^ 2 := by simp only [sq]; group
        _ = 1 := by rw [W2.b_sq, H.sq_t, one_mul]
    have h1 : (d₁ * (b * t)) ^ 2 = d₁ * ((b * t) * d₁ * (b * t)⁻¹) * (b * t) ^ 2 := by
      simp only [sq]
      group
    rw [h1, H.bt_conj_D W W2 hD hb hd₁, hbt2, mul_one] at hu2
    have hθ1 : theta t d₁ = 1 := by
      calc theta t d₁ = (theta t d₁ * d₁) * d₁⁻¹ := by group
        _ = (d₁ * theta t d₁) * d₁⁻¹ := by rw [hcomm]
        _ = d₁ * (theta t d₁ * d₁⁻¹) := by group
        _ = 1 := hu2
    exact (H.D_theta_eq_one_iff W W2 hD hd₁).1 hθ1
  · have h := hBLK s (mem_sup_left hs)
    rw [hu] at h
    have hts : t * s = s * t := H.comm_of_mem_L (W.S_le hs)
    have e : (d₁ * (b * t)) * s * (d₁ * (b * t))⁻¹ * s⁻¹ =
        (d₁ * b) * (t * s * t⁻¹) * (d₁ * b)⁻¹ * s⁻¹ := by group
    rw [e, show t * s * t⁻¹ = s by rw [hts]; group] at h
    exact h

theorem ThCyc.not_extremal_Db
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B) {g d₁ : G} (hd₁ : d₁ ∈ D)
    (hu : g⁻¹ * t * g = d₁ * b)
    (hR : 2 * Nat.card S ≤ Nat.card ↥((S ⊔ Bp A t) ⊓ centralizer ({g⁻¹ * t * g} : Set G)))
    (huP : g⁻¹ * t * g ∈ S ⊔ Bp A t) : False := by
  obtain ⟨hnD, hcard, -⟩ := H.ext_extremal_of_card W W2 hD hAb hZ (H.isPGroup_S_sup_Bp W)
    (sup_le le_sup_left (zpowers_le.2 (mem_sup_right (H.t_mem_Bp W W2)))) le_sup_right
    (H.S_sup_Bp_le_normalizer W) hR huP
  have hCeq := inf_centralizer_mul_eq hD.comm (v := b) hd₁
  refine H.false_of_card_eq W W2 hD hEl (g := g) ?_ hnD ?_
  · rw [hu, ← hCeq]
    exact inf_le_right
  · rw [← hCeq, ← hu]
    exact hcard

end

end CFSG.EvenSporadicStandard.ThStd
