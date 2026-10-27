module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma9Para
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Core

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem inf_centralizer_eq_bot_of_hyperplane_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1294 : Lemma12_9_4_F4) (h1297 : Lemma12_9_7_F4)
    {T L V : Subgroup G} {n : ℕ} (hcx : Cx1291 G T L V n) {g : G}
    (hAT : CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G) ≤ T)
    (hidx : (CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G)).relIndex
      (CFSG.conjugate V g) = 2)
    (hAV : ⁅CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G), V⁆ ≠ ⊥) :
    CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) =
      ⊥ := by
  classical
  have h1298 := lemma12_9_8_F4 h1222 h37 h38 h39 h1294 h1297
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨hVT, hTV⟩ := hyp.le_and_normalizes_F4 h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  have : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2) }
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2)⟩
  have hNV := normalizer_le_of_hyp1223 h37 h38 h39 hyp hTV hVp
  set A := CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G) with hAdef
  have hAVg : A ≤ CFSG.conjugate V g := inf_le_left
  have hAsq : ∀ x ∈ A, x ^ 2 = 1 := fun x hx => LinearS3.sq_eq_one_of_mem_conjugate hx.1
  have hVgV : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥ := fun h => hAV (le_bot_iff.1
    (h ▸ Subgroup.commutator_mono hAVg le_rfl))
  have hbot := inf_conjugate_eq_bot_of_commutator_ne_bot_F4 h1298 hcx hVgV
  have hVM : V ≤ Subgroup.normalizer (L : Set G) := hVT.trans hyp.normalizes

  have hF2 : V ⊓ Subgroup.normalizer (A : Set G) = V ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_antisymm (fun i hi => ⟨hi.1, ?_⟩)
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
    show i ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : a * i * a⁻¹ * i⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTV (hAT ha)) i).1 hi.1) (V.inv_mem hi.1)
    have h2 : a * i * a⁻¹ * i⁻¹ ∈ A := by
      have h3 : i * a⁻¹ * i⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hi.2 _).1 (inv_mem ha)
      rw [show a * i * a⁻¹ * i⁻¹ = a * (i * a⁻¹ * i⁻¹) by group]
      exact mul_mem ha h3
    have h4 : a * i * a⁻¹ * i⁻¹ = 1 := by
      have h5 : a * i * a⁻¹ * i⁻¹ ∈ V ⊓ CFSG.conjugate V g := ⟨h1, hAVg h2⟩
      rwa [hbot, Subgroup.mem_bot] at h5
    calc a * i = (a * i * a⁻¹ * i⁻¹) * (i * a) := by group
      _ = i * a := by rw [h4, one_mul]

  have hF3 : ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic B →
      V ⊓ Subgroup.centralizer (B : Set G) = V ⊓ Subgroup.centralizer (A : Set G) := by
    intro B hBA hBc
    have hN := LinearS3.centralizer_le_normalizer_conjugate
      (fun B hB hc => centralizer_le_normalizer_of_not_isCyclic_F4 h1222 h1297 hcx hB hc) g
      (hBA.trans hAVg) hBc
    refine le_antisymm ?_ (inf_le_inf_left _ (Subgroup.centralizer_le hBA))
    rw [← hF2]
    intro v hv
    refine ⟨hv.1, ?_⟩
    have h1 : v ∈ Subgroup.normalizer (CFSG.conjugate V g : Set G) ⊓
        Subgroup.normalizer (Subgroup.normalizer (L : Set G) : Set G) :=
      ⟨hN hv.2, Subgroup.le_normalizer (hVM hv.1)⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf h1
  have hnle : ¬ V ≤ Subgroup.centralizer (A : Set G) := fun h => by
    apply hAV
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 h

  set A₁ := A ⊓ Subgroup.centralizer (V : Set G) with hA₁def
  have hA₁le : Nat.card A₁ ≤ 2 := by
    by_contra h
    push Not at h
    have h4 : 4 ≤ Nat.card A₁ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 ((hT2.to_le hAT).to_le
        (inf_le_left : A₁ ≤ A))
      rw [hk] at h ⊢
      have : 2 ≤ k := by
        by_contra hk2
        interval_cases k <;> norm_num at h
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
    have hBc := LinearS3.not_isCyclic_of_four_le (B := A₁) (fun x hx => hAsq x hx.1) h4
    have h1 := hF3 A₁ inf_le_left hBc
    apply hnle
    intro v hv
    have hv' : v ∈ V ⊓ Subgroup.centralizer (A₁ : Set G) := by
      refine ⟨hv, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hb.2 v hv).symm
    rw [h1] at hv'
    exact hv'.2
  by_contra hA₁ne
  have hA₁2 : Nat.card A₁ = 2 := by
    have h1 : Nat.card A₁ ≠ 1 := fun h => hA₁ne (Subgroup.card_eq_one.1 h)
    have h2 : 0 < Nat.card A₁ := Nat.card_pos
    omega

  obtain ⟨V₁, hV₁⟩ := exists_tsub hT2 hsq hab hTV hcard 1 (by omega)
  obtain ⟨k, hVk, hV₁k⟩ := exists_conjugate_eq_of_card_eq_two hcx.hyp hV₁
    (inf_le_left.trans hAVg) hA₁2
  have hU := h1294 G T L V n hcx V₁ hV₁
  have hUab : ∀ x ∈ u128 V V₁, ∀ y ∈ u128 V V₁, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(u128 V V₁)) ⟨y, hy⟩)
  have hG₁U : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    le_normalizer_conjClosure V _

  have hUkab : ∀ x ∈ CFSG.conjugate (u128 V V₁) k, ∀ y ∈ CFSG.conjugate (u128 V V₁) k,
      x * y = y * x := by
    intro x hx y hy
    have h1 := hUab _ (SteinbergBS.mem_conjugate_iff.1 hx) _ (SteinbergBS.mem_conjugate_iff.1 hy)
    calc x * y = k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * y * k⁻¹) * (k * x * k⁻¹)) * k := by rw [h1]
      _ = y * x := by group
  have hVUk : V ≤ Subgroup.normalizer (CFSG.conjugate (u128 V V₁) k : Set G) := by
    intro v hv
    rw [mem_normalizer_conjugate_iff]
    apply hG₁U
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxA : k⁻¹ * x * k ∈ CFSG.conjugate V₁ k := by
      rw [SteinbergBS.mem_conjugate_iff, show k * (k⁻¹ * x * k) * k⁻¹ = x by group]
      exact hx
    rw [hV₁k] at hxA
    have h1 := Subgroup.mem_centralizer_iff.1 hxA.2 v hv
    calc x * (k * v * k⁻¹) = k * ((k⁻¹ * x * k) * v) * k⁻¹ := by group
      _ = k * (v * (k⁻¹ * x * k)) * k⁻¹ := by rw [h1]
      _ = k * v * k⁻¹ * x := by group
  have hAUk : A ≤ CFSG.conjugate (u128 V V₁) k := by
    rw [← hVk] at hAVg
    exact hAVg.trans (LinearS3.conjugate_mono (le_conjClosure V _) k)

  set C := ⁅V, A⁆ with hCdef
  have hCV : C ≤ V := by
    rw [hCdef, Subgroup.commutator_le]
    intro v hv a ha
    rw [commutatorElement_def, show v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) by group]
    exact mul_mem hv ((Subgroup.mem_normalizer_iff.1 (hTV (hAT ha)) _).1 (inv_mem hv))
  have hCU : C ≤ CFSG.conjugate (u128 V V₁) k := by
    rw [hCdef, Subgroup.commutator_le]
    intro v hv a ha
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hVUk hv) a).1 (hAUk ha)) (inv_mem (hAUk ha))
  have hCne : C ≠ ⊥ := by
    rw [hCdef, Subgroup.commutator_comm]
    exact hAV

  have hCc : IsCyclic C := by
    by_contra hnc
    have hN := centralizer_le_normalizer_of_not_isCyclic_F4 h1222 h1297 hcx hCV hnc
    have hVg : CFSG.conjugate V g ≤ Subgroup.normalizer (L : Set G) := by
      intro x hx
      apply hNV
      apply hN
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      rw [← hVk] at hx
      exact hUkab c (hCU hc) x (LinearS3.conjugate_mono (le_conjClosure V _) k hx)
    have hAeq : A = CFSG.conjugate V g := inf_eq_left.2 hVg
    rw [hAeq, Subgroup.relIndex_self] at hidx
    norm_num at hidx
  have hC2 : Nat.card C = 2 := by
    have h1 := SteinbergBS.card_le_two_of_isCyclic hCc (fun x hx => hsq x (hCV hx))
    have h2 : Nat.card C ≠ 1 := fun h => hCne (Subgroup.card_eq_one.1 h)
    have h3 : 0 < Nat.card C := Nat.card_pos
    omega

  have hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a := by
    intro a ha c hc
    by_cases hc1 : c = 1
    · rw [hc1, mul_one, one_mul]
    have h1 : a * c * a⁻¹ ∈ C := by
      have h2 : a * c * a⁻¹ * c⁻¹ ∈ C := by
        rw [hCdef, Subgroup.commutator_comm]
        have := Subgroup.commutator_mem_commutator ha (hCV hc)
        rwa [commutatorElement_def] at this
      have h3 := C.mul_mem h2 hc
      rwa [show a * c * a⁻¹ * c⁻¹ * c = a * c * a⁻¹ by group] at h3
    have h2 : a * c * a⁻¹ ≠ 1 := fun h => hc1 (by
      have := congrArg (fun x => a⁻¹ * x * a) h
      simpa [mul_assoc] using this)
    have e := SteinbergBS.eq_of_card_le_two hC2.le h1 hc h2 hc1
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [e]

  obtain ⟨v₀, hv₀V, hv₀C⟩ : ∃ v ∈ V, v ∉ Subgroup.centralizer (A : Set G) := by
    by_contra h
    push Not at h
    exact hnle h
  obtain ⟨R, hRC, -, hcardA⟩ := exists_commutator_image (A := A) (W := C) (v := v₀)
    (fun x hx y hy => hab x (hCV hx) y (hCV hy)) hAC
    (fun a ha => by
      rw [hCdef, Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator ha hv₀V
      rwa [commutatorElement_def] at this)

  have hker : A ⊓ Subgroup.centralizer ({v₀} : Set G) ≤ A₁ := by
    intro a ha
    by_contra haA₁
    have hB : ¬ IsCyclic ↥(Subgroup.zpowers a ⊔ A₁) := by
      refine LinearS3.not_isCyclic_of_four_le (fun x hx => hAsq x ?_) ?_
      · exact (sup_le ((Subgroup.zpowers_le).2 ha.1) inf_le_left) hx
      · have hle : Subgroup.zpowers a ⊔ A₁ ≤ A := sup_le ((Subgroup.zpowers_le).2 ha.1) inf_le_left
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 ((hT2.to_le hAT).to_le hle)
        have hgt : 2 < Nat.card ↥(Subgroup.zpowers a ⊔ A₁) := by
          by_contra hle2
          push Not at hle2
          have h1 : A₁ = Subgroup.zpowers a ⊔ A₁ :=
            Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hA₁2]; exact hle2)
          exact haA₁ (h1 ▸ (le_sup_left : Subgroup.zpowers a ≤ _) (Subgroup.mem_zpowers a))
        rw [hj] at hgt ⊢
        have : 2 ≤ j := by
          by_contra hj2
          interval_cases j <;> norm_num at hgt
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) this
    have h1 := hF3 _ (sup_le ((Subgroup.zpowers_le).2 ha.1) inf_le_left) hB
    have hv₀B : v₀ ∈ V ⊓ Subgroup.centralizer ((Subgroup.zpowers a ⊔ A₁ : Subgroup G) : Set G) := by
      refine ⟨hv₀V, ?_⟩
      have hle : Subgroup.zpowers a ⊔ A₁ ≤ Subgroup.centralizer ({v₀} : Set G) :=
        sup_le ((Subgroup.zpowers_le).2 ha.2) fun x hx =>
          Subgroup.mem_centralizer_iff.2 fun y hy => by
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact Subgroup.mem_centralizer_iff.1 hx.2 v₀ hv₀V
      show v₀ ∈ Subgroup.centralizer ((Subgroup.zpowers a ⊔ A₁ : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.1 (hle hb) v₀ rfl).symm
    rw [h1] at hv₀B
    exact hv₀C hv₀B.2

  have hcardA' : Nat.card A = 2 ^ (n - 1) := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf (CFSG.conjugate V g))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAVg).toEquiv, LinearS3.card_conjugate,
      hcard] at h1
    have h2 : (A.subgroupOf (CFSG.conjugate V g)).index = 2 := hidx
    rw [h2] at h1
    have h3 : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have h1 := Subgroup.card_le_of_le hRC
  have h2 := Subgroup.card_le_of_le hker
  rw [hC2] at h1
  rw [hA₁2] at h2
  have h3 : 2 ^ (n - 1) ≤ 4 := by
    rw [← hcardA', hcardA]
    calc Nat.card R * _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2
      _ = 4 := by norm_num
  have h4 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.Quasithin.H13
