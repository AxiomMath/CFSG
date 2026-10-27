module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Sylow
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Subgroup

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_of_lt [Finite G] {p : ℕ} [Fact p.Prime] {T P : Subgroup G}
    (hP : IsPGroup p P) (hTP : T ≤ P) (hne : T ≠ P) :
    ∃ x ∈ P, x ∉ T ∧ x ∈ normalizer (T : Set G) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  set T' := T.subgroupOf P with hT'
  have hlt : T' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne ?_
    apply le_antisymm hTP
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ T' := h ▸ mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨x, hxN, hxT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent T' hlt)
  refine ⟨x, x.2, fun h => hxT (Subgroup.mem_subgroupOf.2 h), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have := (Subgroup.mem_normalizer_iff.1 hxN ⟨g, hTP hg⟩).1 (Subgroup.mem_subgroupOf.2 hg)
    exact Subgroup.mem_subgroupOf.1 this
  · intro hg
    have hgP : g ∈ P := by
      have h1 : (x : G) * g * (x : G)⁻¹ ∈ P := hTP hg
      have h2 : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x := by group
      rw [h2]
      exact P.mul_mem (P.mul_mem (P.inv_mem x.2) h1) x.2
    have := (Subgroup.mem_normalizer_iff.1 hxN ⟨g, hgP⟩).2 (Subgroup.mem_subgroupOf.2 hg)
    exact Subgroup.mem_subgroupOf.1 this

theorem eq_of_isPGroup_of_not_dvd [Finite G] {T K P : Subgroup G}
    (hi : ¬ 2 ∣ (T.subgroupOf K).index) (hP : IsPGroup 2 P) (hTP : T ≤ P) (hPK : P ≤ K) :
    P = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Subgroup.relIndex_mul_relIndex T P K hTP hPK
  have hdvd : T.relIndex P ∣ T.relIndex K := ⟨_, hmul.symm⟩
  obtain ⟨k, hk⟩ := (hP.to_le (le_refl P)).exists_card_eq
  have hdvd2 : T.relIndex P ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card T P
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  have hj0 : j = 0 := by
    by_contra h0
    apply hi
    have : 2 ∣ T.relIndex P := by
      rw [hj]
      exact dvd_pow_self 2 h0
    exact this.trans hdvd
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_antisymm hj hTP

theorem isMaximal_of_conj [Finite G] {t : G} {TH T : Subgroup G} (htTH : t ∈ TH)
    (hTHc : TH ≤ centralizer ({t} : Set G))
    (hTHi : ¬ 2 ∣ (TH.subgroupOf (centralizer ({t} : Set G))).index)
    (hTH : TH ≤ T) (hconj : ∀ g : G, g * t * g⁻¹ ∈ T → ∃ y ∈ T, g * t * g⁻¹ = y * t * y⁻¹) :
    ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Q hQ hTQ
  by_contra hne
  obtain ⟨x, hxQ, hxT, hxN⟩ := exists_mem_normalizer_of_lt hQ hTQ (Ne.symm hne)
  have hxt : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hxN t).1 (hTH htTH)
  obtain ⟨y, hyT, hxy⟩ := hconj x hxt
  have hz : y⁻¹ * x ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y⁻¹ * x * t = y⁻¹ * (x * t * x⁻¹) * x := by group
      _ = y⁻¹ * (y * t * y⁻¹) * x := by rw [hxy]
      _ = t * (y⁻¹ * x) := by group
  have hzQ : y⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (hTQ hyT)) hxQ
  have heq := eq_of_isPGroup_of_not_dvd hTHi (hQ.to_le inf_le_left)
    (le_inf (hTH.trans hTQ) hTHc) inf_le_right
  have hzTH : y⁻¹ * x ∈ TH := heq ▸ (⟨hzQ, hz⟩ : y⁻¹ * x ∈ Q ⊓ centralizer ({t} : Set G))
  apply hxT
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact T.mul_mem hyT (hTH hzTH)

theorem pResidual_eq_top_of_simple [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : CFSG.Quasithin.pResidual 2 G = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have h2 : IsPGroup 2 G := fun x => by
      obtain ⟨k, hk⟩ := hp x
      rw [h, mem_bot] at hk
      exact ⟨k, hk⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : Nontrivial (center G) := h2.center_nontrivial
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hz | hz
    · rw [hz] at hc
      obtain ⟨x, y, hxy⟩ := hc
      exact hxy (Subsingleton.elim x y)
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (mem_center_iff.mp (hz ▸ mem_top a : a ∈ center G) b).symm
  · rw [h]

theorem false_of_transfer [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {t : G} (ht : orderOf t = 2) {T M : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTmax : ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T) (hMT : M ≤ T)
    (hidx : M.relIndex T = 2) (hM : ∀ g : G, g * t * g⁻¹ ∉ M) : False := by
  let P : Sylow 2 G :=
    { toSubgroup := T, isPGroup' := hT2, is_maximal' := fun {Q} hQ hle => hTmax Q hQ hle }
  have h := CFSG.Quasithin.thompson_transfer_lemma P hMT hidx ht
    (fun x hx => hM x⁻¹ (by simpa using hx))
  rw [pResidual_eq_top_of_simple hG hnab] at h
  exact h (mem_top t)

variable {W : Subgroup G} {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}

variable (W φ) in
@[expose] def rhoPre (Y : Subgroup GL12) : Subgroup G := (Y.comap (rho W φ)).map (NW W).subtype

variable (W φ) in
@[expose] def rhoOn {A : Subgroup G} (hA : A ≤ NW W) : A →* GL12 :=
  (rho W φ).comp (Subgroup.inclusion hA)

theorem mem_rhoPre {Y : Subgroup GL12} {g : G} :
    g ∈ rhoPre W φ Y ↔ g ∈ NW W ∧ rhoG W φ g ∈ Y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [Subgroup.coe_subtype, rhoG_of_mem x.2]
    exact hx
  · rintro ⟨hg, hy⟩
    rw [rhoG_of_mem hg] at hy
    exact ⟨⟨g, hg⟩, hy, rfl⟩

theorem rhoOn_apply {A : Subgroup G} (hA : A ≤ NW W) (a : A) :
    rhoOn W φ hA a = rhoG W φ a := (rhoG_of_mem (hA a.2)).symm

theorem range_rhoOn {A : Subgroup G} (hA : A ≤ NW W) : (rhoOn W φ hA).range = rhoImg W φ A := by
  ext y
  rw [MonoidHom.mem_range, mem_rhoImg hA]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, (rhoOn_apply hA a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rhoOn_apply hA ⟨a, ha⟩⟩

theorem relIndex_inf_rhoPre {T : Subgroup G} (hT : T ≤ NW W) {S Y : Subgroup GL12}
    (hTS : rhoImg W φ T = S) (hY : Y.relIndex S = 2) :
    (T ⊓ rhoPre W φ Y).relIndex T = 2 := by
  have e : (T ⊓ rhoPre W φ Y).subgroupOf T = Y.comap (rhoOn W φ hT) := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, rhoOn_apply, Subgroup.mem_inf, mem_rhoPre]
    exact ⟨fun h => h.2.2, fun h => ⟨a.2, hT a.2, h⟩⟩
  rw [Subgroup.relIndex, e, Subgroup.index_comap, range_rhoOn, hTS, hY]

theorem card_W (φ : W ≃* Multiplicative (Fin 12 → ZMod 2)) : Nat.card W = 2 ^ 12 := by
  rw [Nat.card_congr φ.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem isPGroup_rhoImg {P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ NW W) :
    IsPGroup 2 (rhoImg W φ P) :=
  (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).map _

theorem inf_centralizer_eq_W (φ : W ≃* Multiplicative (Fin 12 → ZMod 2)) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hWT : W ≤ T)
    (hN1 : ∀ S : Subgroup G, S ≤ centralizer (W : Set G) → IsPGroup 2 S → S ≤ W) :
    T ⊓ centralizer (W : Set G) = W := by
  refine le_antisymm (inf_centralizer_le_W hT2 hN1) (le_inf hWT ?_)
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact congrArg Subtype.val (W_comm φ ⟨v, hv⟩ ⟨w, hw⟩)

theorem isMaximal_of_offender [Finite G]
    (hN1 : ∀ S : Subgroup G, S ≤ centralizer (W : Set G) → IsPGroup 2 S → S ≤ W)
    {T : Subgroup G} (hTN : T ≤ NW W) (hT2 : IsPGroup 2 T) (hWT : W ≤ T) {S : Subgroup GL12}
    (hTS : rhoImg W φ T = S)
    (hSmax : ∀ Y : Subgroup GL12, Y ≤ Xof W φ → IsPGroup 2 Y → S ≤ Y → Y = S)
    (hoff : ∀ A : Subgroup GL12, A ≤ S → (∀ x ∈ A, x * x = 1) → A ≠ ⊥ →
      Nat.card A * Nat.card ↥(Set.univ ∩ fixV A) ≤ 2 ^ 11) :
    ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmaxN : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P ≤ NW W → P = T := by
    intro P hP hTP hPN
    have hPS : rhoImg W φ P = S := by
      refine hSmax _ (rhoImg_le_Xof P) (isPGroup_rhoImg hP hPN) ?_
      rw [← hTS]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := (mem_rhoImg hTN).1 hy
      exact (mem_rhoImg hPN).2 ⟨a, hTP ha, rfl⟩
    have hcP := card_eq_card_rhoImg_mul (φ := φ) hPN
    have hcT := card_eq_card_rhoImg_mul (φ := φ) hTN
    rw [hPS, inf_centralizer_eq_W φ hP (hWT.trans hTP) hN1] at hcP
    rw [hTS, inf_centralizer_eq_W φ hT2 hWT hN1] at hcT
    exact (Subgroup.eq_of_le_of_card_ge hTP (by rw [hcP, hcT])).symm
  have huniq : ∀ A : Subgroup G, A ≤ T → (∀ x ∈ A, x * x = 1) → 2 ^ 12 ≤ Nat.card A →
      A = W := by
    intro A hAT hsq hcard
    have hAN : A ≤ NW W := hAT.trans hTN
    have hAW := inf_centralizer_le_W (W := W) (isPGroup_of_sq_eq_one hsq) hN1
    have hc := card_eq_card_rhoImg_mul (φ := φ) hAN
    by_cases hbot : rhoImg W φ A = ⊥
    · rw [hbot, Subgroup.card_bot, one_mul] at hc
      have hAC : A ⊓ centralizer (W : Set G) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hc)
      have hAW' : A ≤ W := hAC ▸ hAW
      exact Subgroup.eq_of_le_of_card_ge hAW' (by rw [card_W φ]; exact hcard)
    · exfalso
      have hle : rhoImg W φ A ≤ S := by
        rw [← hTS]
        intro y hy
        obtain ⟨a, ha, rfl⟩ := (mem_rhoImg hAN).1 hy
        exact (mem_rhoImg hTN).2 ⟨a, hAT ha, rfl⟩
      have hsq' : ∀ y ∈ rhoImg W φ A, y * y = 1 := by
        intro y hy
        obtain ⟨a, ha, rfl⟩ := (mem_rhoImg hAN).1 hy
        rw [← rhoG_mul (hAN ha) (hAN ha), hsq a ha, rhoG_one]
      have hk := card_inf_centralizer_le (φ := φ) hAN hAW
        (fun a ha b hb => commute_of_sq_eq_one hsq ha hb) (Z := Set.univ) (fun _ _ => trivial)
      have h1 := hoff _ hle hsq' hbot
      have h2 : Nat.card A ≤ 2 ^ 11 := hc ▸ (Nat.mul_le_mul_left _ hk).trans h1
      omega
  have hnorm : ∀ g ∈ normalizer (T : Set G), g ∈ NW W := by
    intro g hg
    have hA : W.map (MulAut.conj g).toMonoidHom = W := by
      refine huniq _ ?_ ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hg w).1 (hWT hw)
      · rintro _ ⟨w, hw, rfl⟩
        rw [← map_mul, W_mem_sq φ hw, map_one]
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_W φ]
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have : g * w * g⁻¹ ∈ W.map (MulAut.conj g).toMonoidHom := ⟨w, hw, by simp⟩
      rwa [hA] at this
    · intro hw
      rw [← hA] at hw
      obtain ⟨w', hw', e⟩ := hw
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at e
      have : w' = w := by simpa using e
      rwa [← this]
  intro Q hQ hTQ
  by_contra hne
  obtain ⟨x, hxQ, hxT, hxN⟩ := exists_mem_normalizer_of_lt hQ hTQ (Ne.symm hne)
  have hxW := hnorm x hxN
  have hP : T ⊔ zpowers x = T := hmaxN _ (hQ.to_le (sup_le hTQ ((zpowers_le).2 hxQ)))
    le_sup_left (sup_le hTN ((zpowers_le).2 hxW))
  exact hxT (hP ▸ (le_sup_right : zpowers x ≤ T ⊔ zpowers x) (mem_zpowers x))

end CFSG.EvenSmallLie.OmegaEight.Stage2
