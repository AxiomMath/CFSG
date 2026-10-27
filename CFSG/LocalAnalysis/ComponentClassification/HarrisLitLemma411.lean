module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma411b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma411a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitMacWilliams

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem ncard_pair_le_two {α : Type*} (a b : α) : ({a, b} : Set α).ncard ≤ 2 :=
  (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])

theorem relIndex_ne_zero_of_finite {G : Type*} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 := by
  intro h0
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [h0, zero_mul] at h1
  exact Nat.card_pos.ne' h1.symm

theorem card_centralizer_ge_four_of_sq {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ e ∈ E, e ^ 2 = 1)
    (hcard : Nat.card E = 8) {y : G} (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hy2 : ∀ e ∈ E, y ^ 2 * e = e * y ^ 2) :
    4 ≤ Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) := by
  let δ : ↥E →* G :=
    { toFun := fun e => (e : G)⁻¹ * (y * e * y⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hc1 := hcomm _ (inv_mem b.2) _ (hyE a a.2)
        have hc2 := hcomm _ (inv_mem a.2) _ (inv_mem b.2)
        simp only [Subgroup.coe_mul]
        calc ((a : G) * b)⁻¹ * (y * (a * b) * y⁻¹) =
            ((b : G)⁻¹ * (a : G)⁻¹) * ((y * a * y⁻¹) * (y * b * y⁻¹)) := by group
          _ = ((a : G)⁻¹ * (b : G)⁻¹) * ((y * a * y⁻¹) * (y * b * y⁻¹)) := by rw [hc2]
          _ = (a : G)⁻¹ * ((b : G)⁻¹ * (y * a * y⁻¹)) * (y * b * y⁻¹) := by group
          _ = (a : G)⁻¹ * ((y * a * y⁻¹) * (b : G)⁻¹) * (y * b * y⁻¹) := by rw [hc1]
          _ = (a : G)⁻¹ * (y * a * y⁻¹) * ((b : G)⁻¹ * (y * b * y⁻¹)) := by group }
  have hδ : ∀ e : ↥E, δ e = (e : G)⁻¹ * (y * e * y⁻¹) := fun _ => rfl
  have hker : Nat.card δ.ker = Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    have : δ.ker = (centralizer ({y} : Set G)).subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, hδ, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
      constructor
      · intro h1
        have h2 : y * (e : G) * y⁻¹ = e := by
          calc y * (e : G) * y⁻¹ = (e : G) * ((e : G)⁻¹ * (y * e * y⁻¹)) := by group
            _ = e := by rw [h1, mul_one]
        calc (e : G) * y = (y * e * y⁻¹) * y := by rw [h2]
          _ = y * e := by group
      · intro h1
        rw [← h1]
        group
    rw [this, ← Subgroup.card_map_of_injective E.subtype_injective, subgroupOf_map_subtype,
      inf_comm]
  have hrange : δ.range ≤ E ⊓ centralizer ({y} : Set G) := by
    rintro _ ⟨e, rfl⟩
    rw [hδ]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem e.2) (hyE e e.2), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hd : (e : G)⁻¹ * (y * e * y⁻¹) ∈ E := mul_mem (inv_mem e.2) (hyE e e.2)
    have hd2 := hsq _ hd
    have he2 : y ^ 2 * (e : G) * (y ^ 2)⁻¹ = e := by
      rw [hy2 e e.2]
      group
    have hstep : y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹ = (y * e * y⁻¹)⁻¹ * e := by
      calc y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹ =
          (y * (e : G)⁻¹ * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) := by
            rw [sq]
            group
        _ = (y * e * y⁻¹)⁻¹ * e := by rw [he2]; group
    have hinv' : ((e : G)⁻¹ * (y * e * y⁻¹))⁻¹ = (e : G)⁻¹ * (y * e * y⁻¹) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hd2])
    have hfix : y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹ = (e : G)⁻¹ * (y * e * y⁻¹) := by
      rw [hstep]
      calc (y * e * y⁻¹)⁻¹ * (e : G) = ((e : G)⁻¹ * (y * e * y⁻¹))⁻¹ := by group
        _ = _ := hinv'
    calc (e : G)⁻¹ * (y * e * y⁻¹) * y = (y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹) * y := by
          rw [hfix]
      _ = y * ((e : G)⁻¹ * (y * e * y⁻¹)) := by group
  have h1 := Subgroup.card_ker_mul_card_range δ
  have h2 : Nat.card δ.range ≤ Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hrange
  rw [hker, hcard] at h1
  have h3 : 8 ≤ Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) *
      Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    rw [← h1]
    exact Nat.mul_le_mul_left _ h2
  have hdvd : Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) ∣ 8 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hc : Nat.card (E ⊓ centralizer ({y} : Set G) : Subgroup G) <;> omega

variable {X : Type} [Group X]

structure IsC411 (t : X) (L S : Subgroup X) (w z : X) (V E : Subgroup X) (c : X) : Prop where
  mem : c ∈ V
  not_mem : c ∉ S
  sq_mem : c ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w
  comm : ∀ g ∈ V, c⁻¹ * (g * c * g⁻¹) ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w
  le_E : ∀ x ∈ closure {t, w ^ (orderOf w / 2), z}, x * c = c * x → x ∈ E
  four_le : 4 ≤ Nat.card (closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) :
    Subgroup X)

variable {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem isC411_of_mem [Finite X] (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {Y E : Subgroup X} (hY : IsSylowOf 2 Y ⊤) (hVY : V ≤ Y) (hEY : E ≤ Y)
    (hEn : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hE8 : Nat.card E = 8) (hEV : E ≤ V) {c : X} (hcE : c ∈ E)
    (hcS : c ∉ S) : IsC411 t L S w z V E c := by
  have htS : t ∈ S := h.t_mem hS
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hSY := hSV.trans hVY
  have hC4 := card_centralizer_ge_four hEc hE2 hE8 (fun e he => hEn t (hSY htS) e he) ht2
  have hCX := hσ.inf_centralizer_le_X hY hSY hEY hEn hE2
  have hcC : c ∉ E ⊓ centralizer ({t} : Set X) := by
    intro hc'
    apply hcS
    rw [← hσ.inf_centralizer_t hV hSV]
    exact Subgroup.mem_inf.mpr ⟨hEV hcE, hc'.2⟩
  have hCidx : (E ⊓ centralizer ({t} : Set X)).relIndex E = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := E ⊓ centralizer ({t} : Set X)) (K := E)
    rw [inf_of_le_left (inf_le_left.trans le_rfl : E ⊓ centralizer ({t} : Set X) ≤ E), hE8]
      at h1
    have hne1 : (E ⊓ centralizer ({t} : Set X)).relIndex E ≠ 1 := fun h' =>
      hcC (Subgroup.relIndex_eq_one.mp h' hcE)
    have hne0 : (E ⊓ centralizer ({t} : Set X)).relIndex E ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact absurd h1 (by norm_num)
    by_contra hne2
    have : 3 * 4 ≤ (E ⊓ centralizer ({t} : Set X)).relIndex E *
        Nat.card (E ⊓ centralizer ({t} : Set X) : Subgroup X) :=
      Nat.mul_le_mul (by omega) hC4
    omega
  have hTn : ∀ g ∈ V, ∀ x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w,
      g * x * g⁻¹ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
    fun g hg x hx => (mem_normalizer_iff.mp (hV.le hg) x).mp hx
  refine ⟨hEV hcE, hcS, ?_, ?_, ?_, ?_⟩
  · rw [hE2 c hcE]
    exact one_mem _
  · intro g hg
    have hyE := hEn g (hVY hg) c hcE
    have hyC : g * c * g⁻¹ ∉ E ⊓ centralizer ({t} : Set X) := by
      intro hy
      apply hcS
      have h1 := hTn g⁻¹ (inv_mem hg) _ (hσ.X_le_T (hCX hy))
      have : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
      rw [this] at h1
      exact hσ.T_le h1
    exact hσ.X_le_T (hCX (inv_mul_mem_of_relIndex_two hCidx hcE hyE hcC hyC))
  ·
    intro x hxX hxc
    have hCF : E ⊓ centralizer ({t} : Set X) ≤
        closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) := fun y hy =>
      Subgroup.mem_inf.mpr ⟨hCX hy, mem_centralizer_singleton_iff.mpr (hEc y hy.1 c hcE)⟩
    have htF : t ∉ closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) := by
      intro ht'
      apply hcS
      rw [← hσ.inf_centralizer_t hV hSV]
      refine Subgroup.mem_inf.mpr ⟨hEV hcE, mem_centralizer_singleton_iff.mpr ?_⟩
      exact (mem_centralizer_singleton_iff.mp ht'.2).symm
    have hFle : Nat.card (closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) :
        Subgroup X) ≤ 4 := by
      have h1 := Subgroup.relIndex_mul_card
        (H := closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X))
        (K := closure {t, w ^ (orderOf w / 2), z})
      rw [inf_of_le_left inf_le_left] at h1
      have h2 := hσ.card_X_le
      have hne1 : (closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X)).relIndex
          (closure {t, w ^ (orderOf w / 2), z}) ≠ 1 := fun h' =>
        htF (Subgroup.relIndex_eq_one.mp h' htX)
      have hne0 : (closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X)).relIndex
          (closure {t, w ^ (orderOf w / 2), z}) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact Nat.card_pos.ne' h1.symm
      by_contra hlt
      have : 2 * 5 ≤ (closure {t, w ^ (orderOf w / 2), z} ⊓
          centralizer ({c} : Set X)).relIndex (closure {t, w ^ (orderOf w / 2), z}) *
          Nat.card (closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) :
            Subgroup X) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have heq := Subgroup.eq_of_le_of_card_ge hCF (hFle.trans hC4)
    have hxF : x ∈ closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) :=
      Subgroup.mem_inf.mpr ⟨hxX, mem_centralizer_singleton_iff.mpr hxc⟩
    rw [← heq] at hxF
    exact hxF.1
  · have hCF : E ⊓ centralizer ({t} : Set X) ≤
        closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) := fun y hy =>
      Subgroup.mem_inf.mpr ⟨hCX hy, mem_centralizer_singleton_iff.mpr (hEc y hy.1 c hcE)⟩
    exact hC4.trans (Subgroup.card_le_of_le hCF)

theorem relIndex_eq_two_of_normal [Finite X] (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hSn : ∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S)
    (hST : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) :
    S.relIndex V = 2 ∧ (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2 := by
  classical
  have htV : t ∈ V := hSV (h.t_mem hS)
  constructor
  · have hsub : {y : X | ∃ v ∈ V, v * t * v⁻¹ = y} ⊆ {t, t * z} := by
      rintro _ ⟨v, hv, rfl⟩
      rcases hσ.conj_t_eq hV.le hST hSn hv with h1 | h1 <;> rw [h1] <;> simp
    have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_pair_le_two t (t * z))
    rw [ncard_conj_orbit V htV, ← inf_relIndex_right, inf_comm,
      hσ.inf_centralizer_t hV hSV] at hle
    have hne1 : S.relIndex V ≠ 1 := fun h1 =>
      hσ.ne_of_isSylowOf_normalizer hV hSV (le_antisymm hSV (Subgroup.relIndex_eq_one.mp h1))
    have hne0 : S.relIndex V ≠ 0 := relIndex_ne_zero_of_finite _ _
    omega
  · have hle := (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.1
    have h1 := Subgroup.relIndex_mul_card (H := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (K := S)
    rw [inf_of_le_left hσ.T_le] at h1
    have hne1 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S ≠ 1 := fun h' =>
      hST (le_antisymm (Subgroup.relIndex_eq_one.mp h') hσ.T_le)
    have hpos : 0 < Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := Nat.card_pos
    have hne0 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S ≠ 0 :=
      relIndex_ne_zero_of_finite _ _
    by_contra hne2
    have : 3 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ≤
        (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S *
          Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem exists_isC411_of_eq [Finite X] (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {E : Subgroup X} (hEX : E = closure {t, w ^ (orderOf w / 2), z})
    (hE8 : Nat.card E = 8) : ∃ c, IsC411 t L S w z V E c := by
  classical
  have hTV : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ V := hσ.T_le.trans hSV
  have hTn : ∀ g ∈ V, ∀ x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w,
      g * x * g⁻¹ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
    fun g hg x hx => (mem_normalizer_iff.mp (hV.le hg) x).mp hx
  suffices hc : ∃ c ∈ V, c ∉ S ∧ c ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ∧
      ∀ g ∈ V, c⁻¹ * (g * c * g⁻¹) ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w by
    obtain ⟨c, hcV, hcS, hc2, hcc⟩ := hc
    refine ⟨c, hcV, hcS, hc2, hcc, fun x hx _ => hEX ▸ hx, ?_⟩
    have hX8 : Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) = 8 := hEX ▸ hE8
    have := card_centralizer_ge_four_of_sq (E := closure {t, w ^ (orderOf w / 2), z})
      (fun a ha b hb => hσ.X_comm ha hb) (fun e he => hσ.sq_eq_one_of_mem_X he) hX8
      (fun e he => (mem_normalizer_iff.mp
        (hσ.normalizer_T_le_normalizer_X (hV.le hcV)) e).mp he)
      (fun e he => mem_centralizer_iff.mp (hσ.X_le_center_T he).2 _ hc2)
    exact this
  by_cases hcase : (∀ v ∈ V, ∀ s ∈ S, v * s * v⁻¹ ∈ S) ∧
      S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w
  ·
    obtain ⟨hSV2, hST2⟩ := hσ.relIndex_eq_two_of_normal hV hSV hcase.1 hcase.2
    have hsq : ∀ v ∈ V, v ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := fun v hv =>
      hσ.sq_mem_T_of_relIndex hKF hKC hV hSV hST2 hSV2 hv
    obtain ⟨c, hcV, hcS⟩ : ∃ c ∈ V, c ∉ S := by
      by_contra hall
      push Not at hall
      exact hσ.ne_of_isSylowOf_normalizer hV hSV (le_antisymm hSV fun x hx => hall x hx)
    refine ⟨c, hcV, hcS, hsq c hcV, fun g hg => ?_⟩
    have : c⁻¹ * (g * c * g⁻¹) = (c ^ 2)⁻¹ * (c * g) ^ 2 * (g ^ 2)⁻¹ := by
      rw [sq, sq, sq]
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (hsq c hcV)) (hsq _ (mul_mem hcV hg)))
      (inv_mem (hsq g hg))
  ·
    set N := (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).subgroupOf V with hNdef
    have hN : N.Normal := by
      rw [hNdef, normal_subgroupOf_iff_le_normalizer hTV]
      exact hV.le
    have hmemN : ∀ x : ↥V, x ∈ N ↔ (x : X) ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := fun x =>
      Subgroup.mem_subgroupOf
    have hQp : IsPGroup 2 (↥V ⧸ N) := hV.isPGroup.to_quotient N
    obtain ⟨v₁, hv₁V, hv₁T⟩ : ∃ v ∈ V, v ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      by_contra hall
      push Not at hall
      exact hσ.ne_of_isSylowOf_normalizer hV hSV
        (le_antisymm hSV fun x hx => hσ.T_le (hall x hx))
    have hnt : Nontrivial (↥V ⧸ N) :=
      ⟨⟨QuotientGroup.mk ⟨v₁, hv₁V⟩, 1, fun h' =>
        hv₁T ((hmemN _).mp ((QuotientGroup.eq_one_iff (N := N) _).mp h'))⟩⟩
    have hcen := hQp.center_nontrivial
    have h2 : 2 ∣ Nat.card (center (↥V ⧸ N)) := by
      rcases (hQp.to_subgroup _).card_eq_or_dvd with h1 | h1
      · exact absurd h1 (Finite.one_lt_card (α := ↥(center (↥V ⧸ N)))).ne'
      · exact h1
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
    obtain ⟨⟨c, hcV⟩, hcq⟩ := QuotientGroup.mk_surjective (q : ↥V ⧸ N)
    have hqo : orderOf (q : ↥V ⧸ N) = 2 := by
      rw [Subgroup.orderOf_coe, hq]
    have hcT : c ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      intro hc'
      have : (q : ↥V ⧸ N) = 1 := by
        rw [← hcq]
        exact (QuotientGroup.eq_one_iff (N := N) _).mpr ((hmemN _).mpr hc')
      rw [this, orderOf_one] at hqo
      exact absurd hqo (by norm_num)
    have hc2 : c ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      have h1 : (QuotientGroup.mk (⟨c, hcV⟩ ^ 2 : ↥V) : ↥V ⧸ N) = 1 := by
        rw [QuotientGroup.mk_pow, hcq, ← hqo, pow_orderOf_eq_one]
      exact (hmemN _).mp ((QuotientGroup.eq_one_iff (N := N) _).mp h1)
    have hcc : ∀ g ∈ V, c⁻¹ * (g * c * g⁻¹) ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      intro g hg
      have hcen' := Subgroup.mem_center_iff.mp q.2 (QuotientGroup.mk ⟨g, hg⟩ : ↥V ⧸ N)
      have h1 : (QuotientGroup.mk ((⟨c, hcV⟩ : ↥V)⁻¹ * (⟨g, hg⟩ * ⟨c, hcV⟩ * (⟨g, hg⟩)⁻¹)) :
          ↥V ⧸ N) = 1 := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcq]
        rw [hcen']
        group
      exact (hmemN _).mp ((QuotientGroup.eq_one_iff (N := N) _).mp h1)
    refine ⟨c, hcV, fun hcS => hcase ⟨fun v hv s hs => ?_, fun hST => hcT (hST ▸ hcS)⟩, hc2,
      hcc⟩
    have hSne : S ≠ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := fun hST => hcT (hST ▸ hcS)
    have hST2 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S = 2 := by
      have hle := (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.1
      have h1 := Subgroup.relIndex_mul_card (H := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (K := S)
      rw [inf_of_le_left hσ.T_le] at h1
      have hne1 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S ≠ 1 := fun h' =>
        hSne (le_antisymm (Subgroup.relIndex_eq_one.mp h') hσ.T_le)
      have hpos : 0 < Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := Nat.card_pos
      have hne0 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S ≠ 0 :=
        relIndex_ne_zero_of_finite _ _
      by_contra hne2
      have : 3 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ≤
          (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex S *
            Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    by_cases hsT : s ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w
    · exact hσ.T_le (hTn v hv s hsT)
    · have hτ := inv_mul_mem_of_relIndex_two hST2 hcS hs hcT hsT
      have h1 := hcc v hv
      have : v * s * v⁻¹ = (c * (c⁻¹ * (v * c * v⁻¹))) * (v * (c⁻¹ * s) * v⁻¹) := by group
      rw [this]
      exact S.mul_mem (S.mul_mem hcS (hσ.T_le h1)) (hσ.T_le (hTn v hv _ hτ))

theorem exists_isBeta411_of_isC411 [Finite X] (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {Y E : Subgroup X} (hY : IsSylowOf 2 Y ⊤) (hEY : E ≤ Y)
    (hEn : ∀ y ∈ Y, ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hE8 : Nat.card E = 8) {c : X}
    (hc : IsC411 t L S w z V E c) : ∃ β, IsBeta411 t L S w z V β := by
  classical
  have hcV := hc.mem
  have hcN := hV.le hcV
  have hcNX := hσ.normalizer_T_le_normalizer_X hcN
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hTV : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ V := hσ.T_le.trans hSV
  have hz2 : z ^ 2 = 1 := by rw [← hσ.z_order, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro hz
    have := hσ.z_order
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  have hzz : z * z = 1 := by rw [← sq, hz2]
  have hcz : c * z * c⁻¹ = z := hσ.conj_z_of_mem_normalizer_T hcN
  have hc2X : ∀ x ∈ closure {t, w ^ (orderOf w / 2), z}, c ^ 2 * x = x * c ^ 2 := fun x hx =>
    mem_centralizer_iff.mp (hσ.X_le_center_T hx).2 _ hc.sq_mem
  have hcS : c ∉ S := hc.not_mem
  have hCt : ∀ v ∈ V, v * t = t * v → v ∈ S := fun v hv hvt => by
    rw [← hσ.inf_centralizer_t hV hSV]
    exact Subgroup.mem_inf.mpr ⟨hv, mem_centralizer_singleton_iff.mpr hvt⟩
  set F := closure {t, w ^ (orderOf w / 2), z} ⊓ centralizer ({c} : Set X) with hF
  have hmemF : ∀ x, x ∈ F ↔ x ∈ closure {t, w ^ (orderOf w / 2), z} ∧ x * c = c * x := by
    intro x
    rw [hF, Subgroup.mem_inf, mem_centralizer_singleton_iff]
  have hzF : z ∈ F := (hmemF z).mpr ⟨hzX, by
    calc z * c = (c * z * c⁻¹) * c := by rw [hcz]
      _ = c * z := by group⟩
  have htF : t ∉ F := fun ht' => hcS (hCt c hcV ((hmemF t).mp ht').2.symm)
  have hF4 : 4 ≤ Nat.card F := hc.four_le
  have hFidx : F.relIndex (closure {t, w ^ (orderOf w / 2), z}) = 2 ∧ Nat.card F = 4 := by
    have h1 : F.relIndex (closure {t, w ^ (orderOf w / 2), z}) * Nat.card F =
        Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) := by
      have := Subgroup.relIndex_mul_card (H := F) (K := closure {t, w ^ (orderOf w / 2), z})
      rwa [inf_of_le_left (inf_le_left : F ≤ closure {t, w ^ (orderOf w / 2), z})] at this
    have h2 := hσ.card_X_le
    have hne1 : F.relIndex (closure {t, w ^ (orderOf w / 2), z}) ≠ 1 := fun h' =>
      htF (Subgroup.relIndex_eq_one.mp h' htX)
    have hne0 : F.relIndex (closure {t, w ^ (orderOf w / 2), z}) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact Nat.card_pos.ne' h1.symm
    have hge2 : 2 * Nat.card F ≤ F.relIndex (closure {t, w ^ (orderOf w / 2), z}) * Nat.card F :=
      Nat.mul_le_mul_right _ (by omega)
    have hle2 : F.relIndex (closure {t, w ^ (orderOf w / 2), z}) ≤ 2 := by
      by_contra hlt
      have : 3 * 4 ≤ F.relIndex (closure {t, w ^ (orderOf w / 2), z}) * Nat.card F :=
        Nat.mul_le_mul (by omega) hF4
      omega
    constructor <;> omega
  obtain ⟨β₀, hβ₀F, hβ₀1, hβ₀z⟩ : ∃ β₀ ∈ F, β₀ ≠ 1 ∧ β₀ ≠ z := by
    by_contra hno
    push Not at hno
    have hsub : (F : Set X) ⊆ {1, z} := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1]
        simp
      · rw [hno x hx hx1]
        simp
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_pair_le_two 1 z)
    rw [← Nat.card_coe_set_eq] at this
    have h4 : Nat.card ((F : Set X)) = Nat.card F := rfl
    omega
  obtain ⟨d, hd⟩ : ∃ d, d = t⁻¹ * (c * t * c⁻¹) := ⟨_, rfl⟩
  have hctX : c * t * c⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
    (mem_normalizer_iff.mp hcNX t).mp htX
  have hdX : d ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rw [hd]
    exact mul_mem (inv_mem htX) hctX
  have hdF : d ∈ F := by
    refine (hmemF d).mpr ⟨hdX, ?_⟩
    have hct2 : c ^ 2 * t * (c ^ 2)⁻¹ = t := by
      rw [hc2X t htX]
      group
    have hd2 := hσ.sq_eq_one_of_mem_X hdX
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by rw [← sq, hd2])
    have hcd : c * d * c⁻¹ = d := by
      calc c * d * c⁻¹ = (c * t * c⁻¹)⁻¹ * (c ^ 2 * t * (c ^ 2)⁻¹) := by
            rw [hd, sq]
            group
        _ = (c * t * c⁻¹)⁻¹ * t := by rw [hct2]
        _ = d⁻¹ := by rw [hd]; group
        _ = d := hdinv
    calc d * c = (c * d * c⁻¹) * c := by rw [hcd]
      _ = c * d := by group
  have hd1 : d ≠ 1 := by
    intro hd1
    apply hcS
    refine hCt c hcV ?_
    have : c * t * c⁻¹ = t := by
      calc c * t * c⁻¹ = t * d := by rw [hd]; group
        _ = t := by rw [hd1, mul_one]
    calc c * t = (c * t * c⁻¹) * c := by group
      _ = t * c := by rw [this]
  obtain ⟨β, hβF, hβ1, hβz, hdβ⟩ : ∃ β ∈ F, β ≠ 1 ∧ β ≠ z ∧ d ≠ β := by
    by_cases hdβ₀ : d = β₀
    · refine ⟨β₀ * z, mul_mem hβ₀F hzF, fun h' => hβ₀z ?_, fun h' => hβ₀1 ?_, fun h' => hz1 ?_⟩
      · calc β₀ = β₀ * z * z := by rw [mul_assoc, hzz, mul_one]
          _ = z := by rw [h', one_mul]
      · calc β₀ = β₀ * z * z⁻¹ := by group
          _ = 1 := by rw [h', mul_inv_cancel]
      · calc z = β₀⁻¹ * (β₀ * z) := by group
          _ = 1 := by rw [← h', hdβ₀, inv_mul_cancel]
    · exact ⟨β₀, hβ₀F, hβ₀1, hβ₀z, hdβ₀⟩
  have hβX : β ∈ closure {t, w ^ (orderOf w / 2), z} := ((hmemF β).mp hβF).1
  have hβc : β * c = c * β := ((hmemF β).mp hβF).2
  have hβzF : β * z ∈ F := mul_mem hβF hzF
  have hβz1 : β * z ≠ 1 := fun h' => hβz (by
    calc β = β * z * z := by rw [mul_assoc, hzz, mul_one]
      _ = z := by rw [h', one_mul])
  have hβzz : β * z ≠ z := fun h' => hβ1 (by
    calc β = β * z * z⁻¹ := by group
      _ = 1 := by rw [h', mul_inv_cancel])
  have hβzβ : β * z ≠ β := fun h' => hz1 (by
    calc z = β⁻¹ * (β * z) := by group
      _ = 1 := by rw [h', inv_mul_cancel])
  have hFset : ∀ x ∈ F, x = 1 ∨ x = z ∨ x = β ∨ x = β * z := by
    have hsub : ({1, z, β, β * z} : Set X) ⊆ (F : Set X) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx]
      · exact one_mem F
      · exact hzF
      · exact hβF
      · exact hβzF
    have hcard4 : ({1, z, β, β * z} : Set X).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hβzβ.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hβz, Ne.symm hβzz⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hz1, Ne.symm hβ1, Ne.symm hβz1⟩
    have hFn : (F : Set X).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hFidx.2
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hFn, hcard4])
    intro x hx
    have hx' : x ∈ ({1, z, β, β * z} : Set X) := by
      rw [heq]
      exact hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx'
  have hβD : β ∉ zpowers t ⊔ (S ⊓ L) := by
    intro hβD'
    obtain ⟨a, c', ha, hc', hac⟩ := hσ.mem_X_tD hβX hβD'
    rcases ha with ha | ha <;> rcases hc' with hc' | hc' <;> rw [ha, hc'] at hac
    · exact hβ1 (by rw [hac, mul_one])
    · exact hβz (by rw [hac, one_mul])
    · exact htF (by rw [mul_one] at hac; rw [← hac]; exact hβF)
    · apply htF
      have : t = β * z⁻¹ := by rw [hac]; group
      rw [this]
      exact mul_mem hβF (inv_mem hzF)
  have hctd : c * t * c⁻¹ = t * z ∨ c * t * c⁻¹ = t * β * z := by
    have hcd : c * t * c⁻¹ = t * d := by rw [hd]; group
    rcases hFset d hdF with h' | h' | h' | h'
    · exact absurd h' hd1
    · left
      rw [hcd, h']
    · exact absurd h' hdβ
    · right
      rw [hcd, h', mul_assoc]
  have hVF : ∀ g ∈ V, ∀ x ∈ F, g * x * g⁻¹ ∈ F := by
    intro g hg x hx
    obtain ⟨hxX, hxc⟩ := (hmemF x).mp hx
    have hτ : c⁻¹ * (g⁻¹ * c * g) ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      have := hc.comm g⁻¹ (inv_mem hg)
      rwa [inv_inv] at this
    have hxτ : x * (c⁻¹ * (g⁻¹ * c * g)) = (c⁻¹ * (g⁻¹ * c * g)) * x :=
      (mem_centralizer_iff.mp (hσ.X_le_center_T hxX).2 _ hτ).symm
    have hxc' : x * (g⁻¹ * c * g) = (g⁻¹ * c * g) * x := by
      calc x * (g⁻¹ * c * g) = (x * c) * (c⁻¹ * (g⁻¹ * c * g)) := by group
        _ = (c * x) * (c⁻¹ * (g⁻¹ * c * g)) := by rw [hxc]
        _ = c * (x * (c⁻¹ * (g⁻¹ * c * g))) := by group
        _ = c * ((c⁻¹ * (g⁻¹ * c * g)) * x) := by rw [hxτ]
        _ = (g⁻¹ * c * g) * x := by group
    refine (hmemF _).mpr ⟨(mem_normalizer_iff.mp
      (hσ.normalizer_T_le_normalizer_X (hV.le hg)) x).mp hxX, ?_⟩
    calc g * x * g⁻¹ * c = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by rw [hxc']
      _ = c * (g * x * g⁻¹) := by group
  have hβV : ∀ g ∈ V, g * β * g⁻¹ = β ∨ g * β * g⁻¹ = β * z := by
    intro g hg
    rcases hFset _ (hVF g hg β hβF) with h' | h' | h' | h'
    · exact absurd (by
        calc β = g⁻¹ * (g * β * g⁻¹) * g := by group
          _ = 1 := by rw [h']; group) hβ1
    · exact absurd (by
        calc β = g⁻¹ * (g * β * g⁻¹) * g := by group
          _ = g⁻¹ * z * g := by rw [h']
          _ = z := by
            have := hσ.conj_z_of_mem_normalizer_T (inv_mem (hV.le hg))
            rwa [inv_inv] at this) hβz
    · exact Or.inl h'
    · exact Or.inr h'
  have hβV' : β ∈ V := hTV (hσ.X_le_T hβX)
  have hrel : (V ⊓ centralizer ({β} : Set X)).relIndex V ≤ 2 := by
    have hsub : {y : X | ∃ g ∈ V, g * β * g⁻¹ = y} ⊆ {β, β * z} := by
      rintro _ ⟨g, hg, rfl⟩
      rcases hβV g hg with h' | h' <;> rw [h'] <;> simp
    have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_pair_le_two β (β * z))
    rwa [ncard_conj_orbit V hβV', ← inf_relIndex_right, inf_comm] at hle
  have hTβ : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ centralizer ({β} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hσ.X_le_center_T hβX).2 y hy)
  have hcCβ : c ∈ V ⊓ centralizer ({β} : Set X) :=
    Subgroup.mem_inf.mpr ⟨hcV, mem_centralizer_singleton_iff.mpr hβc.symm⟩
  have hinf := hσ.inf_centralizer_inf_t hKC hV hSV hβX hβD
  refine ⟨β, ⟨hβX, hβD, ?_, ⟨c, hcCβ, hcS, hc.sq_mem, hctd⟩, ?_,
    hσ.isSylowOf_inf_centralizer hKF hV hβX,
    fun g hg hgX => hσ.exists_conj_of_mem_centralizer hKF hV hβX hg hgX, hinf, hrel,
    twoPart_le_of_mem hY hEY hEn hE8 (hc.le_E β hβX hβc) hβ1, ?_⟩⟩
  ·
    intro g hg
    obtain ⟨v, hv, hvt⟩ := hσ.exists_conj_V_of_mem_X hKF hV (hg ▸ hβX)
    have hvtβ : v * t * v⁻¹ = β := hvt.trans hg
    have h1 : v⁻¹ * c * v ∈ S := by
      refine hCt _ (V.mul_mem (V.mul_mem (V.inv_mem hv) hcV) hv) ?_
      calc v⁻¹ * c * v * t = v⁻¹ * (c * (v * t * v⁻¹)) * v := by group
        _ = v⁻¹ * (c * β) * v := by rw [hvtβ]
        _ = v⁻¹ * (β * c) * v := by rw [hβc]
        _ = v⁻¹ * ((v * t * v⁻¹) * c) * v := by rw [hvtβ]
        _ = t * (v⁻¹ * c * v) := by group
    apply hcS
    have h2 := hc.comm v⁻¹ (inv_mem hv)
    rw [inv_inv] at h2
    have h3 : c = (v⁻¹ * c * v) * (c⁻¹ * (v⁻¹ * c * v))⁻¹ := by group
    rw [h3]
    exact S.mul_mem h1 (S.inv_mem (hσ.T_le h2))
  ·
    refine lt_of_le_of_ne (le_inf hTV hTβ) fun heq => hcS (hσ.T_le ?_)
    rw [heq]
    exact hcCβ
  ·
    rintro ⟨g, hgX, hne⟩
    obtain ⟨b, hb, hbt⟩ := hσ.exists_conj_V_of_mem_X hKF hV hgX
    have hbC : b ∉ V ⊓ centralizer ({β} : Set X) := fun hb' => hne b hb' hbt
    have hbβ : b * β * b⁻¹ = β * z := by
      rcases hβV b hb with h' | h'
      · refine absurd (Subgroup.mem_inf.mpr ⟨hb, mem_centralizer_singleton_iff.mpr ?_⟩) hbC
        calc b * β = (b * β * b⁻¹) * b := by group
          _ = β * b := by rw [h']
      · exact h'
    have hidx : (V ⊓ centralizer ({β} : Set X)).relIndex V = 2 := by
      have hne1 : (V ⊓ centralizer ({β} : Set X)).relIndex V ≠ 1 := fun h1 =>
        hbC (Subgroup.relIndex_eq_one.mp h1 hb)
      have hne0 : (V ⊓ centralizer ({β} : Set X)).relIndex V ≠ 0 :=
        relIndex_ne_zero_of_finite _ _
      omega
    have hST : S = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      by_contra hST
      obtain ⟨s, hsS, hsT⟩ : ∃ s ∈ S, s ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
        by_contra hall
        push Not at hall
        exact hST (le_antisymm (fun x hx => hall x hx) hσ.T_le)
      have hsC : s ∉ V ⊓ centralizer ({β} : Set X) := by
        intro hs'
        apply hsT
        rw [← hinf]
        exact Subgroup.mem_inf.mpr ⟨hs', hS.le hsS⟩
      have hbs := inv_mul_mem_of_relIndex_two hidx (inv_mem hb) (inv_mem (hSV hsS))
        (fun h' => hbC (inv_mem_iff.mp h')) (fun h' => hsC (inv_mem_iff.mp h'))
      rw [inv_inv] at hbs
      apply hne _ hbs
      have hst := mem_centralizer_singleton_iff.mp (hS.le hsS)
      rw [← hbt]
      calc b * s⁻¹ * t * (b * s⁻¹)⁻¹ = b * (s⁻¹ * (s * t)) * b⁻¹ := by rw [hst]; group
        _ = b * t * b⁻¹ := by group
    refine ⟨hST, ?_⟩
    by_contra hall
    push Not at hall
    have hbtX : b * t * b⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
      (mem_normalizer_iff.mp (hσ.normalizer_T_le_normalizer_X (hV.le hb)) t).mp htX
    have hbtF : b * t * b⁻¹ ∉ F := by
      intro h'
      apply htF
      have := hVF b⁻¹ (inv_mem hb) _ h'
      have h2 : b⁻¹ * (b * t * b⁻¹) * b⁻¹⁻¹ = t := by group
      rwa [h2] at this
    have heF := inv_mul_mem_of_relIndex_two hFidx.1 htX hbtX htF hbtF
    have hte : b * t * b⁻¹ = t * (t⁻¹ * (b * t * b⁻¹)) := by group
    have he1 : t⁻¹ * (b * t * b⁻¹) ≠ 1 := by
      intro h'
      apply hbC
      have hbS : b ∈ S := hCt b hb (by
        have h2 : b * t * b⁻¹ = t := by rw [hte, h', mul_one]
        calc b * t = (b * t * b⁻¹) * b := by group
          _ = t * b := by rw [h2])
      rw [hST] at hbS
      exact le_inf hTV hTβ hbS
    have hb2t : b ^ 2 * t * (b ^ 2)⁻¹ = t := by
      have hb2 := hσ.T_le (hall b hb)
      have := mem_centralizer_singleton_iff.mp (hS.le hb2)
      calc b ^ 2 * t * (b ^ 2)⁻¹ = t * b ^ 2 * (b ^ 2)⁻¹ := by rw [this]
        _ = t := by group
    set e := t⁻¹ * (b * t * b⁻¹) with he
    have heX : e ∈ closure {t, w ^ (orderOf w / 2), z} := ((hmemF e).mp heF).1
    have he2 := hσ.sq_eq_one_of_mem_X heX
    have hebe : b * e * b⁻¹ = e := by
      have h1 : t * e * (b * e * b⁻¹) = t := by
        calc t * e * (b * e * b⁻¹) = (b * t * b⁻¹) * (b * e * b⁻¹) := by rw [← hte]
          _ = b * (t * e) * b⁻¹ := by group
          _ = b * (b * t * b⁻¹) * b⁻¹ := by rw [← hte]
          _ = b ^ 2 * t * (b ^ 2)⁻¹ := by rw [sq]; group
          _ = t := hb2t
      have h2 : b * e * b⁻¹ = e⁻¹ := by
        calc b * e * b⁻¹ = (t * e)⁻¹ * (t * e * (b * e * b⁻¹)) := by group
          _ = (t * e)⁻¹ * t := by rw [h1]
          _ = e⁻¹ := by group
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq, he2])
    have hbz : b * z * b⁻¹ = z := hσ.conj_z_of_mem_normalizer_T (hV.le hb)
    have hez : e = z := by
      rcases hFset e heF with h' | h' | h' | h'
      · exact absurd h' he1
      · exact h'
      · exfalso
        apply hz1
        have : β * z = β := by rw [← hbβ, ← h', hebe]
        calc z = β⁻¹ * (β * z) := by group
          _ = 1 := by rw [this, inv_mul_cancel]
      · exfalso
        apply hz1
        have h3 : b * (β * z) * b⁻¹ = β := by
          calc b * (β * z) * b⁻¹ = (b * β * b⁻¹) * (b * z * b⁻¹) := by group
            _ = β * z * z := by rw [hbβ, hbz]
            _ = β := by rw [mul_assoc, hzz, mul_one]
        rw [← h', hebe] at h3
        calc z = β⁻¹ * (β * z) := by group
          _ = 1 := by rw [← h', h3, inv_mul_cancel]
    have hbtz : b * t * b⁻¹ = t * z := by rw [hte, hez]
    rcases hctd with h' | h'
    ·
      apply hbC
      have h1 : c⁻¹ * b ∈ S := hCt _ (V.mul_mem (V.inv_mem hcV) hb) (by
        have h2 : (c⁻¹ * b) * t * (c⁻¹ * b)⁻¹ = t := by
          calc (c⁻¹ * b) * t * (c⁻¹ * b)⁻¹ = c⁻¹ * (b * t * b⁻¹) * c := by group
            _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hbtz, h']
            _ = t := by group
        calc c⁻¹ * b * t = ((c⁻¹ * b) * t * (c⁻¹ * b)⁻¹) * (c⁻¹ * b) := by group
          _ = t * (c⁻¹ * b) := by rw [h2])
      rw [hST] at h1
      have : b = c * (c⁻¹ * b) := by group
      rw [this]
      exact mul_mem hcCβ (le_inf hTV hTβ h1)
    ·
      apply hbC
      have hzβ : z * β = β * z := hσ.X_comm hzX hβX
      have h1 : c⁻¹ * b * c ∈ S := hCt _ (V.mul_mem (V.mul_mem (V.inv_mem hcV) hb) hcV) (by
        have h2 : (c⁻¹ * b * c) * t * (c⁻¹ * b * c)⁻¹ = t := by
          calc (c⁻¹ * b * c) * t * (c⁻¹ * b * c)⁻¹ =
              c⁻¹ * (b * (c * t * c⁻¹) * b⁻¹) * c := by group
            _ = c⁻¹ * (b * (t * β * z) * b⁻¹) * c := by rw [h']
            _ = c⁻¹ * ((b * t * b⁻¹) * (b * β * b⁻¹) * (b * z * b⁻¹)) * c := by group
            _ = c⁻¹ * (t * z * (β * z) * z) * c := by rw [hbtz, hbβ, hbz]
            _ = c⁻¹ * (t * (z * β) * (z * z)) * c := by group
            _ = c⁻¹ * (t * β * z) * c := by rw [hzβ, hzz]; group
            _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [h']
            _ = t := by group
        calc c⁻¹ * b * c * t = ((c⁻¹ * b * c) * t * (c⁻¹ * b * c)⁻¹) * (c⁻¹ * b * c) := by
              group
          _ = t * (c⁻¹ * b * c) := by rw [h2])
      rw [hST] at h1
      have h2 := (mem_normalizer_iff.mp hcN _).mp h1
      have h3 : c * (c⁻¹ * b * c) * c⁻¹ = b := by group
      rw [h3] at h2
      exact le_inf hTV hTβ h2

theorem exists_isBeta411 [Finite X] (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (hX : ¬ SectionalRankLeFour X) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) : ∃ β, IsBeta411 t L S w z V β := by
  obtain ⟨Y, hY, hVY⟩ := exists_isSylowOf_ge hV.isPGroup (le_top : V ≤ ⊤)
  have hSY := hSV.trans hVY
  obtain ⟨E, hEY, hEn, hEc, hE2, hE8⟩ := exists_normal_E8 hX hY
  have hEN := hσ.le_normalizer_T hKC hY hSY hEY hEn hEc hE2
  have hYN : Y ⊓ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) = V :=
    hV.eq_of_le (le_inf hVY hV.le) inf_le_right (hY.isPGroup.to_le inf_le_left)
  have hEV : E ≤ V := by
    rw [← hYN]
    exact le_inf hEY hEN
  by_cases hES : E ≤ S
  · have hEX := hσ.eq_X_of_le_S hSY hES hEn hE2 hE8
    obtain ⟨c, hc⟩ := hσ.exists_isC411_of_eq hKF hKC hV hSV hEX hE8
    exact hσ.exists_isBeta411_of_isC411 hKF hKC hV hSV hY hEY hEn hE8 hc
  · obtain ⟨c, hcE, hcS⟩ := IsConcreteLE.not_le_iff_exists.mp hES
    exact hσ.exists_isBeta411_of_isC411 hKF hKC hV hSV hY hEY hEn hE8
      (hσ.isC411_of_mem hV hSV hY hVY hEY hEn hEc hE2 hE8 hEV hcE hcS)

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
