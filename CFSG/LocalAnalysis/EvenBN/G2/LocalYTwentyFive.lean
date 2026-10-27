module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyFour

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_commutator_of {H K : Subgroup G} {g : G}
    (hgen : ∀ h ∈ H, ∀ k ∈ K, g * ⁅h, k⁆ * g⁻¹ ∈ ⁅H, K⁆) {y : G} (hy : y ∈ ⁅H, K⁆) :
    g * y * g⁻¹ ∈ ⁅H, K⁆ := by
  rw [Subgroup.commutator_def] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    exact hgen a ha b hb
  | one => simp
  | mul y z _ _ hy hz =>
    rw [show g * (y * z) * g⁻¹ = g * y * g⁻¹ * (g * z * g⁻¹) by group]
    exact mul_mem hy hz
  | inv y _ hy =>
    rw [show g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ by group]
    exact inv_mem hy

theorem le_normalizer_commutator_left [Finite G] (H K : Subgroup G) :
    H ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := fun x hx =>
  mem_normalizer_of_conj_mem fun _ hy => conj_mem_commutator_of (fun a ha b hb => by
    rw [show x * ⁅a, b⁆ * x⁻¹ = ⁅x * a, b⁆ * ⁅x, b⁆⁻¹ by
      simp only [commutatorElement_def]; group]
    exact mul_mem (commutator_mem_commutator (mul_mem hx ha) hb)
      (inv_mem (commutator_mem_commutator hx hb))) hy

theorem mem_normalizer_commutator [Finite G] {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem fun _ hy => conj_mem_commutator_of (fun a ha b hb => by
    rw [show g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ by
      simp only [commutatorElement_def]; group]
    exact commutator_mem_commutator ((mem_normalizer_iff.1 hH a).1 ha)
      ((mem_normalizer_iff.1 hK b).1 hb)) hy

theorem conj_conj_t {j x w t : G} (hjt : j * t = t * j) (hx : x * t * x⁻¹ = t * w) :
    (j * x * j⁻¹) * t * (j * x * j⁻¹)⁻¹ = t * (j * w * j⁻¹) := by
  have hjt' : j⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  calc (j * x * j⁻¹) * t * (j * x * j⁻¹)⁻¹ = j * (x * (j⁻¹ * t * j) * x⁻¹) * j⁻¹ := by group
    _ = j * (t * w) * j⁻¹ := by rw [hjt', hx]
    _ = j * t * w * j⁻¹ := by group
    _ = t * (j * w * j⁻¹) := by rw [hjt]; group

theorem mem_of_mem_commutator_of_forall [Finite G] {V N J : Subgroup G} (hNV : N ≤ V)
    (hVN : V ≤ normalizer (N : Set G)) (hab : ∀ x ∈ V, ∀ y ∈ V, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hJV : J ≤ normalizer (V : Set G)) (hJN : J ≤ normalizer (N : Set G))
    (hcop : Nat.Coprime (Nat.card J) (Nat.card V)) {c : G} (hc : c ∈ ⁅V, J⁆)
    (hcJ : ∀ j ∈ J, c⁻¹ * (j * c * j⁻¹) ∈ N) : c ∈ N := by
  classical
  have hnorm : (N.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff hNV).2
    fun a b ha hb => (mem_normalizer_iff.1 (hVN hb) a).1 ha
  let π : V →* V ⧸ N.subgroupOf V := QuotientGroup.mk' _
  have hcomm : ∀ a b : V ⧸ N.subgroupOf V, a * b = b * a := fun a b =>
    QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun y => by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      show ((x : G) * y)⁻¹ * ((y : G) * x) ∈ N
      have := hab _ (inv_mem y.2) _ (inv_mem x.2)
      rwa [show (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹⁻¹ * (x : G)⁻¹⁻¹ =
        ((x : G) * y)⁻¹ * ((y : G) * x) by group] at this
  let _ : CommGroup (V ⧸ N.subgroupOf V) :=
    { (inferInstance : Group (V ⧸ N.subgroupOf V)) with mul_comm := hcomm }
  let _ : Fintype J := Fintype.ofFinite J
  have hconjV : ∀ j ∈ J, ∀ v ∈ V, j * v * j⁻¹ ∈ V := fun j hj v hv =>
    (mem_normalizer_iff.1 (hJV hj) v).1 hv
  let act : J → V →* V := fun j =>
    { toFun := fun v => ⟨(j : G) * v * (j : G)⁻¹, hconjV j j.2 v v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hact : ∀ j : J, N.subgroupOf V ≤ (N.subgroupOf V).comap (act j) := fun j v hv => by
    show ((act j v : V) : G) ∈ N
    exact (mem_normalizer_iff.1 (hJN j.2) v).1 (mem_subgroupOf.1 hv)
  let ac : J → (V ⧸ N.subgroupOf V) →* (V ⧸ N.subgroupOf V) := fun j =>
    QuotientGroup.map _ _ (act j) (hact j)
  have hac : ∀ (j : J) (v : V), ac j (π v) = π (act j v) := fun _ _ => rfl
  have hacmul : ∀ (j k : J) (q : V ⧸ N.subgroupOf V), ac (j * k) q = ac j (ac k q) :=
    fun j k q => QuotientGroup.induction_on q fun v => by
      show π (act (j * k) v) = π (act j (act k v))
      congr 1
      exact Subtype.ext (by
        show ((j * k : J) : G) * v * ((j * k : J) : G)⁻¹ =
          (j : G) * ((k : G) * v * (k : G)⁻¹) * (j : G)⁻¹
        simp only [Subgroup.coe_mul]
        group)
  let σ : V ⧸ N.subgroupOf V → V ⧸ N.subgroupOf V := fun q => ∏ j : J, ac j q
  have hσmul : ∀ a b, σ (a * b) = σ a * σ b := fun a b => by
    simp only [σ, map_mul, Finset.prod_mul_distrib]
  have hσinv : ∀ a, σ a⁻¹ = (σ a)⁻¹ := fun a => by
    simp only [σ, map_inv, Finset.prod_inv_distrib]
  have hσac : ∀ (k : J) a, σ (ac k a) = σ a := fun k a => by
    simp only [σ]
    rw [← Fintype.prod_equiv (Equiv.mulRight k) (fun j => ac (j * k) a) (fun j => ac j a)
      (fun _ => rfl)]
    exact Finset.prod_congr rfl fun j _ => (hacmul j k a).symm
  have hkill : ∀ x (hx : x ∈ ⁅V, J⁆), ∃ hxV : x ∈ V, σ (π ⟨x, hxV⟩) = 1 := by
    intro x hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, j, hj, rfl⟩ := hy
      have hmem : ⁅v, j⁆ ∈ V := by
        rw [commutatorElement_def, show v * j * v⁻¹ * j⁻¹ = v * (j * v⁻¹ * j⁻¹) by group]
        exact mul_mem hv (hconjV j hj _ (inv_mem hv))
      refine ⟨hmem, ?_⟩
      have e : π ⟨⁅v, j⁆, hmem⟩ = π ⟨v, hv⟩ * (ac ⟨j, hj⟩ (π ⟨v, hv⟩))⁻¹ := by
        rw [hac, ← map_inv, ← map_mul]
        congr 1
        exact Subtype.ext (by
          show ⁅v, j⁆ = v * (j * v * j⁻¹)⁻¹
          rw [commutatorElement_def]
          group)
      rw [e, hσmul, hσinv, hσac, mul_inv_cancel]
    | one =>
      refine ⟨one_mem V, ?_⟩
      show σ (π 1) = 1
      simp only [σ, map_one, Finset.prod_const_one]
    | mul y z _ _ hy hz =>
      obtain ⟨hyV, hy'⟩ := hy
      obtain ⟨hzV, hz'⟩ := hz
      refine ⟨mul_mem hyV hzV, ?_⟩
      show σ (π (⟨y, hyV⟩ * ⟨z, hzV⟩)) = 1
      rw [map_mul, hσmul, hy', hz', one_mul]
    | inv y _ hy =>
      obtain ⟨hyV, hy'⟩ := hy
      refine ⟨inv_mem hyV, ?_⟩
      show σ (π (⟨y, hyV⟩)⁻¹) = 1
      rw [map_inv, hσinv, hy', inv_one]
  obtain ⟨hcV, hσc⟩ := hkill c hc
  have hfixq : ∀ j : J, ac j (π ⟨c, hcV⟩) = π ⟨c, hcV⟩ := fun j => by
    rw [hac]
    refine (QuotientGroup.eq.2 ?_).symm
    rw [mem_subgroupOf]
    exact hcJ j j.2
  have h1 : σ (π ⟨c, hcV⟩) = π ⟨c, hcV⟩ ^ Fintype.card J := by
    simp only [σ, hfixq, Finset.prod_const, Finset.card_univ]
  rw [h1] at hσc
  have h2 : π ⟨c, hcV⟩ ^ Nat.card (V ⧸ N.subgroupOf V) = 1 := pow_card_eq_one'
  have hord : orderOf (π ⟨c, hcV⟩) = 1 := by
    have d1 : orderOf (π ⟨c, hcV⟩) ∣ Nat.card J := by
      rw [Nat.card_eq_fintype_card]
      exact orderOf_dvd_of_pow_eq_one hσc
    have d2 : orderOf (π ⟨c, hcV⟩) ∣ Nat.card V :=
      (orderOf_dvd_of_pow_eq_one h2).trans (Subgroup.card_quotient_dvd_card _)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left d1 hcop) d2
  have h3 : π ⟨c, hcV⟩ = 1 := orderOf_eq_one_iff.1 hord
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)

theorem coe_sup_eq_mul {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer' hAB x hx
    exact Set.mem_mul.2 ⟨a, ha, b, hb, rfl⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Torus

variable {K : Type} [Field K]
  [Finite K]

omit [Finite G] in
theorem odd_card_J [CharP K 2] (d : G2Data L K) : Odd (Nat.card d.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := not_dvd_card_torusGroup (τ := .G2) (K := K) 2
  rw [G2Data.J, d.card_image (Model.J_le_adjointGroup K)]
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)

theorem coprime_card_J [CharP K 2] (d : G2Data L K) {P : Subgroup G} (hP : IsPGroup 2 P) :
    Nat.Coprime (Nat.card d.J) (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 (odd_card_J d))

theorem eq_one_of_mem_U_of_forall_J₂ [CharP K 2] (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {x : G} (hx : x ∈ d.U) (hfix : ∀ k ∈ d.J₂, k * x = x * k) :
    x = 1 := by
  by_contra hx1
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  have h92 := d.yamada_3_9_2_G (i := 1) (k := 0) (by decide)
  have hle : d.J₂ ≤ ⊥ := by
    rw [← (h92.2 (Or.inr (by decide))).1, ← h92.1 x hx hx1]
    exact fun k hk => Subgroup.mem_inf.2 ⟨hk, mem_centralizer_singleton_iff.2 (hfix k hk)⟩
  have hc := (d.yamada_3_9_1_G 1).2
  rw [show d.Ji 1 = d.J₂ from rfl, le_bot_iff.1 hle, Subgroup.card_bot] at hc
  omega

end Torus

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem J_le_centralizer_inf_normalizer_S (h : Setup G L f t) (d : G2Data L K) :
    d.J ≤ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) := fun j hj => by
  have hj' : j ∈ L ⊓ normalizer (d.S : Set G) := by
    rw [d.yamada_3_13_1_G.2.2]
    exact mem_sup_left hj
  exact Subgroup.mem_inf.2 ⟨h.L_le_centralizer (Subgroup.mem_inf.1 hj').1,
    (Subgroup.mem_inf.1 hj').2⟩

theorem J_le_normalizer_W (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (d.W : Set G) := fun j hj => by
  have hjC := h.J_le_centralizer_inf_normalizer_S d hj
  exact (h.normalizer_tY_le d hK hD).1 (h.centralizer_inf_normalizer_Y_le d
    (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hjC).1,
      (h.centralizer_inf_normalizer_S_le d hK hD).2.2 hjC⟩))

theorem J₄_facts (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.J₄ ≤ d.J ∧ Nat.card d.J₄ = Nat.card K - 1 ∧ d.J₄ ≤ normalizer (d.rootGroup g2v : Set G) ∧
      ∀ x ∈ d.rootGroup g2v, x ≠ 1 → ∀ j ∈ d.J₄, j * x = x * j → j = 1 := by
  obtain ⟨hJ₂J, -, hC, -⟩ := h.J₂_facts d hK
  have hJ₄J : d.J₄ ≤ d.J := d.image_mono inf_le_left
  have h92 := d.yamada_3_9_2_G (i := 3) (k := 1) (by decide)
  obtain ⟨hbot, -⟩ := h92.2 (Or.inr (by decide))
  refine ⟨hJ₄J, (d.yamada_3_9_1_G 3).2, fun j hj => ?_, fun x hx hx1 j hj hjx => ?_⟩
  · rw [← hC]
    refine Common.mem_normalizer_inf
      (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d (hJ₄J hj))).2
      (Subgroup.le_normalizer (mem_centralizer_iff.2 fun y hy => ?_))
    exact J_mul_comm d (hJ₂J hy) (hJ₄J hj)
  · have hj' : j ∈ d.Ji 3 ⊓ centralizer {x} :=
      Subgroup.mem_inf.2 ⟨hj, mem_centralizer_singleton_iff.2 hjx⟩
    rw [h92.1 x hx hx1, hbot] at hj'
    exact (Subgroup.mem_bot).1 hj'

omit [Finite G] in
theorem Y_inf_rootGroup_v (d : G2Data L K) : d.Y ⊓ d.rootGroup g2v = ⊥ := by
  obtain ⟨-, -, hW, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hAS : d.rootGroup g2v ≤ d.S := (le_sup_left.trans hW.le).trans (hWF.trans (hFD.trans hDS))
  have hAc : Nat.card (d.rootGroup g2v) = Nat.card K :=
    (d.card_image (rootSubgroup_le_adjointGroup (K := K) (τ := .G2) g2v)).trans
      (card_rootSubgroup (τ := .G2) (K := K) g2v)
  have h1 := Common.card_sup_mul_card_inf_eq (A := d.Y) (B := d.rootGroup g2v)
    (hAS.trans d.S_le_normalizers.2.1)
  rw [sup_comm, hW, d.cards.2.2.2.1, d.cards.2.1, hAc] at h1
  have hq : 0 < Nat.card K ^ 3 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  refine Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_left hq ?_)
  rw [h1]
  ring

theorem mem_Y_of_forall_J₄ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {w : G} (hw : w ∈ d.W)
    (hfix : ∀ k ∈ d.J₄, w⁻¹ * (k * w * k⁻¹) ∈ d.Y) : w ∈ d.Y := by
  obtain ⟨hJ₄J, hcard, hJA, hreg⟩ := h.J₄_facts d hK
  obtain ⟨-, -, hWdef, -⟩ := d.yamada_defs
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hAY := Y_inf_rootGroup_v d
  have hAS : d.rootGroup g2v ≤ d.S :=
    (le_sup_left.trans hWdef.le).trans (hWF.trans (hFD.trans hDS))
  rw [← hWdef] at hw
  obtain ⟨a, ha, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer' (hAS.trans d.S_le_normalizers.2.1) _ hw
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
    exact hy
  exfalso
  have hall : ∀ k ∈ d.J₄, k = 1 := fun k hk => by
    refine hreg a ha ha1 k hk ?_
    have hkY : k ∈ normalizer (d.Y : Set G) := (h.centralizer_inf_normalizer_S_le d hK hD).2.2
      (h.J_le_centralizer_inf_normalizer_S d (hJ₄J hk))
    have hmem : a⁻¹ * (k * a * k⁻¹) ∈ d.Y ⊓ d.rootGroup g2v := by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hJA hk) _).1 ha)⟩
      rw [show a⁻¹ * (k * a * k⁻¹) =
        y * ((a * y)⁻¹ * (k * (a * y) * k⁻¹)) * (k * y * k⁻¹)⁻¹ by group]
      exact mul_mem (mul_mem hy (hfix k hk)) (inv_mem ((mem_normalizer_iff.1 hkY _).1 hy))
    rw [hAY, Subgroup.mem_bot] at hmem
    calc k * a = a * (a⁻¹ * (k * a * k⁻¹)) * k := by group
      _ = a * k := by rw [hmem, mul_one]
  have hbot : d.J₄ = ⊥ := eq_bot_iff.2 fun k hk => (Subgroup.mem_bot).2 (hall k hk)
  have h4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  rw [hbot, Subgroup.card_bot] at hcard
  omega

theorem wb_mem_normalizer_J (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.wb ∈ normalizer (d.J : Set G) := by
  have hcl : closure ({Model.wa K, Model.wb K} : Set (ModGL .G2 K)) ≤ adjointGroup .G2 K := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    exacts [Model.wa_mem_adjointGroup K, Model.wb_mem_adjointGroup K]
  have hN : closure ({Model.wa K, Model.wb K} : Set (ModGL .G2 K)) ≤
      normalizer (Model.J K : Set (ModGL .G2 K)) := fun x hx => by
    have : x ∈ adjointGroup .G2 K ⊓ normalizer (Model.J K : Set (ModGL .G2 K)) := by
      rw [(Model.yamada_3_7 (hK ▸ h.four_le)).1]
      exact mem_sup_right hx
    exact (Subgroup.mem_inf.1 this).2
  have := d.image_le_normalizer hcl (Model.J_le_adjointGroup K) hN
  rw [d.image_closure_wa_wb] at this
  exact this (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem eq_one_of_mem_yamadaU₁_of_forall_J₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaU₁ d t)
    (hfix : ∀ k ∈ d.J₂, k * x = x * k) : x = 1 := by
  obtain ⟨hJ₂J, -⟩ := h.J₂_facts d hK
  obtain ⟨-, -, -, -, -, hcross, -⟩ := hD.exists_coords hK
  have hkt : ∀ k ∈ d.J₂, k * t = t * k := fun k hk => mem_centralizer_singleton_iff.1
    (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d (hJ₂J hk))).1
  have hc : x⁻¹ * t * x * t = 1 := by
    refine h.eq_one_of_mem_U_of_forall_J₂ d hK (hcross hx) fun k hk => ?_
    have hkx := hfix k hk
    have hkx' : k * x⁻¹ = x⁻¹ * k := by
      calc k * x⁻¹ = x⁻¹ * (x * k) * x⁻¹ := by group
        _ = x⁻¹ * (k * x) * x⁻¹ := by rw [hkx]
        _ = x⁻¹ * k := by group
    calc k * (x⁻¹ * t * x * t) = k * x⁻¹ * t * x * t := by group
      _ = x⁻¹ * k * t * x * t := by rw [hkx']
      _ = x⁻¹ * (k * t) * x * t := by group
      _ = x⁻¹ * (t * k) * x * t := by rw [hkt k hk]
      _ = x⁻¹ * t * (k * x) * t := by group
      _ = x⁻¹ * t * (x * k) * t := by rw [hkx]
      _ = x⁻¹ * t * x * (k * t) := by group
      _ = x⁻¹ * t * x * (t * k) := by rw [hkt k hk]
      _ = x⁻¹ * t * x * t * k := by group
  have hxt : x ∈ centralizer ({t} : Set G) := by
    have e1 : t * x * t = x := by
      calc t * x * t = x * (x⁻¹ * t * x * t) := by group
        _ = x := by rw [hc, mul_one]
    rw [mem_centralizer_singleton_iff]
    calc x * t = t * x * t * t := by rw [e1]
      _ = t * x * (t * t) := by group
      _ = t * x := by rw [h.t_mul_t, mul_one]
  have hxU : x ∈ d.U := by
    rw [← hD.inf_centralizer]
    exact Subgroup.mem_inf.2 ⟨hx, hxt⟩
  exact h.eq_one_of_mem_U_of_forall_J₂ d hK hxU hfix

theorem eq_one_of_mem_yamadaY₂_of_forall_J (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaY₂ d t)
    (hfix : ∀ k ∈ d.J, k * x = x * k) : x = 1 := by
  obtain ⟨hJ₂J, -⟩ := h.J₂_facts d hK
  obtain ⟨⟨hU₁U₁', hU₁'C⟩, -⟩ := h.yamada_5_13_1 d hK hD
  have hwbJ := h.wb_mem_normalizer_J d hK
  have hkU₁ : ∀ k ∈ d.J, k ∈ normalizer (yamadaU₁ d t : Set G) := fun k hk =>
    (h.centralizer_inf_normalizer_S_le d hK hD).2.1 (h.J_le_centralizer_inf_normalizer_S d hk)
  have hk' : ∀ k ∈ d.J, d.wb⁻¹ * k * d.wb ∈ d.J := fun k hk => by
    have := (mem_normalizer_iff.1 (inv_mem hwbJ) k).1 hk
    rwa [inv_inv] at this
  have hconj : ∀ k u : G, k * (d.wb * u * d.wb⁻¹) * k⁻¹ =
      d.wb * ((d.wb⁻¹ * k * d.wb) * u * (d.wb⁻¹ * k * d.wb)⁻¹) * d.wb⁻¹ := fun k u => by group
  obtain ⟨u, hu, u', hu', rfl⟩ := Common.exists_mul_of_le_normalizer
    (hU₁'C.trans (Subgroup.centralizer_le_normalizer _)) x hx
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
  have hsplit : ∀ k ∈ d.J, k * u * k⁻¹ = u ∧
      (d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹ = u₀ := fun k hk => by
    have e := hfix k hk
    have hku : k * u * k⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 (hkU₁ k hk) u).1 hu
    have hku₀ : (d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹ ∈ yamadaU₁ d t :=
      (mem_normalizer_iff.1 (hkU₁ _ (hk' k hk)) u₀).1 hu₀
    have e1 : u⁻¹ * (k * u * k⁻¹) = d.wb * (u₀ *
        ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹)⁻¹) * d.wb⁻¹ := by
      calc u⁻¹ * (k * u * k⁻¹) = u⁻¹ * (k * (u * (d.wb * u₀ * d.wb⁻¹)) * k⁻¹) *
            (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)⁻¹ := by group
        _ = d.wb * u₀ * d.wb⁻¹ * (k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹)⁻¹ := by rw [e]; group
        _ = d.wb * (u₀ * ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹)⁻¹) * d.wb⁻¹ := by
          rw [hconj k u₀]; group
    have hmem : u⁻¹ * (k * u * k⁻¹) ∈ yamadaU₁ d t ⊓
        (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) hku, Subgroup.mem_map.2
        ⟨u₀ * ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹)⁻¹,
          mul_mem hu₀ (inv_mem hku₀), ?_⟩⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact e1.symm
    rw [hU₁U₁', Subgroup.mem_bot] at hmem
    have hku' : k * u * k⁻¹ = u := by
      calc k * u * k⁻¹ = u * (u⁻¹ * (k * u * k⁻¹)) := by group
        _ = u := by rw [hmem, mul_one]
    refine ⟨hku', ?_⟩
    have e2 : d.wb * ((d.wb⁻¹ * k * d.wb) * u₀ * (d.wb⁻¹ * k * d.wb)⁻¹) * d.wb⁻¹ =
        d.wb * u₀ * d.wb⁻¹ := by
      rw [← hconj k u₀]
      calc k * (d.wb * u₀ * d.wb⁻¹) * k⁻¹ =
            (k * u * k⁻¹)⁻¹ * (k * (u * (d.wb * u₀ * d.wb⁻¹)) * k⁻¹) := by group
        _ = d.wb * u₀ * d.wb⁻¹ := by rw [hku', e]; group
    exact mul_left_cancel (mul_right_cancel e2)
  have hfix₁ : ∀ v ∈ yamadaU₁ d t, (∀ k ∈ d.J, k * v * k⁻¹ = v) → v = 1 := fun v hv hv' =>
    h.eq_one_of_mem_yamadaU₁_of_forall_J₂ d hK hD hv fun k hk => by
      calc k * v = k * v * k⁻¹ * k := by group
        _ = v * k := by rw [hv' k (hJ₂J hk)]
  have hu1 : u = 1 := hfix₁ u hu fun k hk => (hsplit k hk).1
  have hu₀1 : u₀ = 1 := hfix₁ u₀ hu₀ fun k hk => by
    have hk₂ : d.wb * k * d.wb⁻¹ ∈ d.J := (mem_normalizer_iff.1 hwbJ k).1 hk
    have := (hsplit _ hk₂).2
    rwa [show d.wb⁻¹ * (d.wb * k * d.wb⁻¹) * d.wb = k by group] at this
  rw [hu1, hu₀1]
  group

theorem eq_one_of_mem_yamadaW₂_of_forall_J (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaW₂ d t)
    (hfix : ∀ k ∈ d.J, k * x = x * k) : x = 1 := by
  obtain ⟨hJ₄J, -⟩ := h.J₄_facts d hK
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hWY₂ : d.W ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hWF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have hkY₂ : ∀ k ∈ d.J₄, k ∈ normalizer (yamadaY₂ d t : Set G) := fun k hk =>
    (h.normalizer_tY_le d hK hD).2.1 (h.J₄_le_normalizer_tY d hk)
  obtain ⟨w, hw, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hWY₂ x hx
  have hwY : w ∈ d.Y := by
    refine h.mem_Y_of_forall_J₄ d hK hD hw fun k hk => ?_
    rw [← h.W_inf_yamadaY₂ d hK hD]
    have hkw : k * w * k⁻¹ ∈ d.W := (mem_normalizer_iff.1 (h.J_le_normalizer_W d hK hD
      (hJ₄J hk)) w).1 hw
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hw) hkw, ?_⟩
    have e : k * (w * y) * k⁻¹ = w * y := by
      rw [hfix k (hJ₄J hk)]
      group
    rw [show w⁻¹ * (k * w * k⁻¹) = y * (k * y * k⁻¹)⁻¹ by
      calc w⁻¹ * (k * w * k⁻¹) = w⁻¹ * (k * (w * y) * k⁻¹) * (k * y * k⁻¹)⁻¹ := by group
        _ = y * (k * y * k⁻¹)⁻¹ := by rw [e]; group]
    exact mul_mem hy (inv_mem ((mem_normalizer_iff.1 (hkY₂ k hk) y).1 hy))
  exact h.eq_one_of_mem_yamadaY₂_of_forall_J d hK hD
    (mul_mem (h.Y_le_yamadaY₂ d hK hD hwY) hy) hfix

theorem yamadaL₃_inf_yamadaR₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₃ d t ⊓ yamadaR₂ d t = yamadaL₂ d t := by
  obtain ⟨hL₂L₃, -, -, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
  have hML₂ : d.M ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d hK)
  refine le_antisymm (fun x hx => ?_) (le_inf hL₂L₃ le_sup_left)
  obtain ⟨hxL₃, hxR₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨l, hl, s, hs, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaL₂ d) _ hxR₂
  have hsM : s ∈ d.M := by
    rw [← hL₃S]
    refine Subgroup.mem_inf.2 ⟨?_, hs⟩
    have := mul_mem (inv_mem (hL₂L₃ hl)) hxL₃
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hl (hML₂ hsM)

theorem yamadaL₂_inf_yamadaE₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaL₂ d t ⊓ yamadaE₃ d t = yamadaE₂ d t := by
  obtain ⟨hE₂E₃, -⟩ := h.yamadaE₃_facts hW d hK hD
  refine le_antisymm (fun x hx => ?_) (le_inf (h.yamadaE₂_le_yamadaL₂ d hK hD).2 hE₂E₃)
  obtain ⟨hxL₂, hxE₃⟩ := Subgroup.mem_inf.1 hx
  rw [← h.yamadaL₂_inf_yamadaC₂ d hK hD]
  refine Subgroup.mem_inf.2 ⟨hxL₂, ?_⟩
  rw [(h.yamadaR₃_facts hW d hK hD).2.2.2.2]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hxE₃).2).2,
    (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) hxL₂⟩

theorem yamadaV₃_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaV₂ d t ≤ yamadaV₃ d t ∧ yamadaV₃ d t ≤ yamadaE₃ d t ∧
      yamadaV₃ d t ⊓ yamadaL₂ d t = yamadaV₂ d t ∧ yamadaV₃ d t ⊓ yamadaR₂ d t = yamadaV₂ d t ∧
      Nat.card (yamadaV₃ d t) = 2 * Nat.card K ^ 6 ∧ yamadaV₃ d t ⊔ yamadaL₂ d t = yamadaL₃ d t ∧
      yamadaV₃ d t ≤ normalizer (yamadaL₂ d t : Set G) ∧
      yamadaV₃ d t ≤ normalizer (yamadaW₂ d t : Set G) ∧
      yamadaV₃ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, hE₃eq, hV₃E₂, hE₃V₃, -, -, -, -⟩ := h.yamada_5_30_1_E₃ hW d hK hD
  obtain ⟨hE₂E₃, -, -, -, -, hcE₃, -⟩ := h.yamadaE₃_facts hW d hK hD
  obtain ⟨hL₂L₃, -⟩ := h.yamadaL₃_facts hW d hK hD
  have hV₂V₃ : yamadaV₂ d t ≤ yamadaV₃ d t := le_sup_right
  have hV₂E₂ : yamadaV₂ d t ≤ yamadaE₂ d t := hV₃E₂.ge.trans inf_le_right
  have hV₃E₃ : yamadaV₃ d t ≤ yamadaE₃ d t := le_sup_left.trans hE₃eq.ge
  have hE₃L₃ : yamadaE₃ d t ≤ yamadaL₃ d t := inf_le_left
  have hV₃N : yamadaV₃ d t ≤ normalizer (yamadaV₂ d t : Set G) :=
    (hV₃E₃.trans hE₃L₃).trans (LieType.BorelTits.pCoreOf_le 2 _)
  have hV₃L₂ : yamadaV₃ d t ⊓ yamadaL₂ d t = yamadaV₂ d t := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf hV₂V₃ (hV₂E₂.trans (h.yamadaE₂_le_yamadaL₂ d hK hD).2))
    obtain ⟨hxV, hxL⟩ := Subgroup.mem_inf.1 hx
    have hxE₂ : x ∈ yamadaE₂ d t := by
      rw [← h.yamadaL₂_inf_yamadaE₃ hW d hK hD]
      exact Subgroup.mem_inf.2 ⟨hxL, hV₃E₃ hxV⟩
    rw [← hV₃E₂]
    exact Subgroup.mem_inf.2 ⟨hxV, hxE₂⟩
  have hV₃R₂ : yamadaV₃ d t ⊓ yamadaR₂ d t = yamadaV₂ d t := by
    refine le_antisymm (fun x hx => ?_) (hV₃L₂.ge.trans (inf_le_inf_left _ le_sup_left))
    obtain ⟨hxV, hxR⟩ := Subgroup.mem_inf.1 hx
    rw [← hV₃L₂, ← h.yamadaL₃_inf_yamadaR₂ hW d hK hD]
    exact Subgroup.mem_inf.2 ⟨hxV, Subgroup.mem_inf.2 ⟨(hV₃E₃.trans hE₃L₃) hxV, hxR⟩⟩
  have hq : 0 < Nat.card K := Nat.card_pos
  obtain ⟨hC₂c, hE₂c, hV₂c⟩ := h.card_yamadaC₂_E₂_V₂ d hK hD
  have hV₃c : Nat.card (yamadaV₃ d t) = 2 * Nat.card K ^ 6 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaV₃ d t) (B := yamadaE₂ d t)
      (hE₂E₃.trans hE₃V₃)
    rw [← hE₃eq, hV₃E₂, hcE₃, hV₂c, hE₂c] at h1
    refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card K ^ 6 by positivity) ?_
    rw [← h1]
    ring
  have hV₃NL₂ : yamadaV₃ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
    hV₃N.trans (h.normalizer_le_normalizer_yamadaL₂ hW d hK hD)
  have hsup : yamadaV₃ d t ⊔ yamadaL₂ d t = yamadaL₃ d t := by
    have hle : yamadaV₃ d t ⊔ yamadaL₂ d t ≤ yamadaL₃ d t :=
      sup_le (hV₃E₃.trans hE₃L₃) hL₂L₃
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaL₂ d t) (B := yamadaV₃ d t) hV₃NL₂
    rw [inf_comm, hV₃L₂, h.card_yamadaL₂ d hK, hV₃c, hV₂c, sup_comm] at h1
    rw [(h.card_yamadaL₃_R₃ hW d hK hD).1]
    have h2 : Nat.card (yamadaV₃ d t ⊔ yamadaL₂ d t : Subgroup G) = 2 * Nat.card K ^ 8 := by
      refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card K ^ 5 by positivity) ?_
      rw [h1]
      ring
    exact h2.ge
  exact ⟨hV₂V₃, hV₃E₃, hV₃L₂, hV₃R₂, hV₃c, hsup, hV₃NL₂,
    hV₃N.trans (h.normalizer_yamadaV₂_le hW d hK hD).1,
    hV₃N.trans (h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ hW d hK hD)⟩

theorem J_le_normalizer_yamadaV₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    d.J ≤ normalizer (yamadaV₃ d t : Set G) ∧ d.J ≤ normalizer (yamadaV₂ d t : Set G) := by
  obtain ⟨hJ₂J, -⟩ := h.J₂_facts d hK
  obtain ⟨hV, hL₃, -, -⟩ := h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  refine ⟨fun j hj => mem_normalizer_sup (Common.mem_normalizer_inf
    (mem_normalizer_sup (hL₃ (hJC hj)) (Subgroup.mem_inf.1 (hJC hj)).2)
    (Subgroup.le_normalizer (mem_centralizer_iff.2 fun y hy => J_mul_comm d (hJ₂J hy) hj)))
    (hV (hJC hj)), fun j hj => hV (hJC hj)⟩

theorem mul_self_mem_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {v : G} (hv : v ∈ yamadaV₂ d t) : v * v ∈ yamadaY₂ d t := by
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hWY₂ : d.W ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hWF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htY₂ := h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hv with
    h1 | ⟨a, ha, rfl⟩
  · obtain ⟨w, hw, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hWY₂ _ h1
    rw [show w * y * (w * y) = w * w * (w⁻¹ * y * w⁻¹⁻¹) * y by group, W_mul_self d hw, one_mul]
    exact mul_mem ((mem_normalizer_iff.1 (inv_mem (hWY₂ hw)) y).1 hy) hy
  · obtain ⟨w, hw, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hWY₂ _ ha
    have hwt : w * t = t * w :=
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hw))
    rw [show w * y * t * (w * y * t) = w * y * (t * w) * y * t by group, ← hwt,
      show w * y * (w * t) * y * t = w * w * (w⁻¹ * y * w⁻¹⁻¹) * (t * y * t⁻¹) * (t * t) by group,
      W_mul_self d hw, h.t_mul_t, one_mul, mul_one]
    exact mul_mem ((mem_normalizer_iff.1 (inv_mem (hWY₂ hw)) y).1 hy)
      ((mem_normalizer_iff.1 htY₂ y).1 hy)

theorem mul_self_mem_yamadaW₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G}
    (hx : x ∈ yamadaV₃ d t) : x * x ∈ yamadaW₂ d t := by
  obtain ⟨-, hV₃E₃, -, hV₃R₂, -, hsup, hV₃L₂, -, hV₃Y₂⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨-, hR₂R₃, hR₃R₂, -, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, -, -, -, -, hsqE₃, -, -⟩ := h.yamada_5_30_1_E₃ hW d hK hD
  obtain ⟨htW, htW'⟩ := h.t_mem_normalizer_yamadaW₂ d hK hD
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hV₃R₃ : yamadaV₃ d t ≤ yamadaR₃ d t := hV₃E₃.trans (inf_le_left.trans le_sup_left)
  have hWY₂ : d.W ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hWF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  rcases (mem_sup_zpowers_iff_of h.t_mul_t htW).1 (hsqE₃ x (hV₃E₃ hx)) with h1 | ⟨a, ha, ha'⟩
  · exact h1
  exfalso
  obtain ⟨w, hw, y₀, hy₀, hwy⟩ :=
    Common.exists_mul_of_le_normalizer' hWY₂ _ ((mem_normalizer_iff.1 htW a).1 ha)
  have hxx : x * x = t * (w * y₀) := by
    rw [ha', ← hwy]
    calc a * t = t * t * a * t⁻¹ := by rw [h.t_mul_t, one_mul, htinv]
      _ = t * (t * a * t⁻¹) := by group
  obtain ⟨g, hg, hgt⟩ := (h.yamada_5_23_2 hW d hK hD).2 w hw
  rw [← hsup] at hg
  obtain ⟨v, hv, l, hl, rfl⟩ := Common.exists_mul_of_le_normalizer' hV₃L₂ _ hg
  have hlN : l ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _ hl
  obtain ⟨y₁, hy₁, hlt⟩ : ∃ y₁ ∈ d.Y, l * t * l⁻¹ = t * y₁ :=
    ⟨_, (h.crossed_mem_Y_iff hW d hK hD ((h.normalizer_tY_le d hK hD).2.2 hlN)).2 hlN,
      h.conj_t_eq_mul_crossed l⟩
  have hvt : v * t * v⁻¹ = t * w * (v * y₁ * v⁻¹)⁻¹ := by
    have e : v * (l * t * l⁻¹) * v⁻¹ = t * w := by
      rw [← hgt]
      group
    rw [hlt] at e
    calc v * t * v⁻¹ = v * (t * y₁) * v⁻¹ * (v * y₁ * v⁻¹)⁻¹ := by group
      _ = t * w * (v * y₁ * v⁻¹)⁻¹ := by rw [e]
  have hvY₂ : v ∈ normalizer (yamadaY₂ d t : Set G) := hV₃Y₂ hv
  have hv₀ : v⁻¹ * y₀ * v ∈ yamadaY₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hvY₂) y₀).1 hy₀
    rwa [inv_inv] at this
  have hy₂ : y₁ * (v⁻¹ * y₀ * v) ∈ yamadaY₂ d t := mul_mem (h.Y_le_yamadaY₂ d hK hD hy₁) hv₀
  have hyV : v⁻¹ * x * v ∈ yamadaV₃ d t := mul_mem (mul_mem (inv_mem hv) hx) hv
  have hyy : v⁻¹ * x * v * (v⁻¹ * x * v) = t * (y₁ * (v⁻¹ * y₀ * v)) := by
    have e1 : v⁻¹ * (t * w) * v = t * y₁ := by
      calc v⁻¹ * (t * w) * v = v⁻¹ * (v * t * v⁻¹ * (v * y₁ * v⁻¹)) * v := by rw [hvt]; group
        _ = t * y₁ := by group
    calc v⁻¹ * x * v * (v⁻¹ * x * v) = v⁻¹ * (x * x) * v := by group
      _ = v⁻¹ * (t * w) * v * (v⁻¹ * y₀ * v) := by rw [hxx]; group
      _ = t * (y₁ * (v⁻¹ * y₀ * v)) := by rw [e1]; group
  have hyN : v⁻¹ * x * v ∈ normalizer (yamadaY₂ d t : Set G) := hV₃Y₂ hyV
  have hyt : ∃ z ∈ yamadaY₂ d t, v⁻¹ * x * v * t * (v⁻¹ * x * v)⁻¹ = t * z := by
    refine ⟨y₁ * (v⁻¹ * y₀ * v) * (v⁻¹ * x * v * (y₁ * (v⁻¹ * y₀ * v))⁻¹ * (v⁻¹ * x * v)⁻¹),
      mul_mem hy₂ ((mem_normalizer_iff.1 hyN _).1 (inv_mem hy₂)), ?_⟩
    calc v⁻¹ * x * v * t * (v⁻¹ * x * v)⁻¹ = v⁻¹ * x * v *
          (v⁻¹ * x * v * (v⁻¹ * x * v) * (y₁ * (v⁻¹ * y₀ * v))⁻¹) * (v⁻¹ * x * v)⁻¹ := by
          rw [hyy]; group
      _ = v⁻¹ * x * v * (v⁻¹ * x * v) * (v⁻¹ * x * v * (y₁ * (v⁻¹ * y₀ * v))⁻¹ *
          (v⁻¹ * x * v)⁻¹) := by group
      _ = t * (y₁ * (v⁻¹ * y₀ * v) * (v⁻¹ * x * v * (y₁ * (v⁻¹ * y₀ * v))⁻¹ *
          (v⁻¹ * x * v)⁻¹)) := by rw [hyy]; group
  have hyR₃ : v⁻¹ * x * v ∈ yamadaR₃ d t := hV₃R₃ hyV
  have hyR₂ : v⁻¹ * x * v ∈ yamadaR₂ d t := by
    have hmem := ((h.yamada_5_21_3 hW d hK hD).2.2.1 (v⁻¹ * x * v)).1 ⟨hR₃R₂ hyR₃, hyt⟩
    obtain ⟨r, hr, n, hn, e⟩ := Common.exists_mul_of_le_normalizer
      (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1 _ hmem
    have hnR : n ∈ yamadaR d t := by
      rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
      refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_inf.1 hn).1⟩
      have hn' : n = r⁻¹ * (v⁻¹ * x * v) := by
        rw [e]
        group
      rw [hn']
      exact (le_sup_left.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge)
        (mul_mem (inv_mem (hR₂R₃ hr)) hyR₃)
    rw [e]
    exact mul_mem hr ((h.yamadaR₂_inf_centralizer d hK).1 hnR)
  have hyV₂ : v⁻¹ * x * v ∈ yamadaV₂ d t := by
    rw [← hV₃R₂]
    exact Subgroup.mem_inf.2 ⟨hyV, hyR₂⟩
  have h1 := h.mul_self_mem_yamadaY₂ d hK hD hyV₂
  rw [hyy] at h1
  have htY₂ : t ∈ yamadaY₂ d t := by
    have := mul_mem h1 (inv_mem hy₂)
    rwa [mul_inv_cancel_right] at this
  exact htW' ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) htY₂)

theorem mem_yamadaL₂_of_forall_J₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G}
    (hx : x ∈ yamadaL₃ d t) (hfix : ∀ k ∈ d.J₄, x⁻¹ * (k * x * k⁻¹) ∈ yamadaL₂ d t) :
    x ∈ yamadaL₂ d t := by
  obtain ⟨hJ₄J, -⟩ := h.J₄_facts d hK
  obtain ⟨-, hJL₃, -⟩ := h.centralizer_inf_normalizer_S_le_normalizers hW d hK hD
  obtain ⟨_, _, φ, hφ, -⟩ := h.yamada_5_23_3 hW d hK hD
  obtain ⟨w, hw, hxw⟩ := (h.yamada_5_23_2 hW d hK hD).1 x hx
  have hwY : w ∈ d.Y := by
    refine h.mem_Y_of_forall_J₄ d hK hD hw fun k hk => ?_
    have hkC := h.J_le_centralizer_inf_normalizer_S d (hJ₄J hk)
    have hkt : k * t = t * k := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hkC).1
    have hkx : k * x * k⁻¹ ∈ yamadaL₃ d t := (mem_normalizer_iff.1 (hJL₃ hkC) _).1 hx
    have hkw : k * w * k⁻¹ ∈ d.W :=
      (mem_normalizer_iff.1 (h.J_le_normalizer_W d hK hD (hJ₄J hk)) w).1 hw
    have h1 := hφ ⟨x, hx⟩ ⟨w, hw⟩ hxw
    have h2 := hφ ⟨k * x * k⁻¹, hkx⟩ ⟨k * w * k⁻¹, hkw⟩ (conj_conj_t hkt hxw)
    have h3 : (QuotientGroup.mk ⟨x, hx⟩ :
        yamadaL₃ d t ⧸ (yamadaL₂ d t).subgroupOf (yamadaL₃ d t)) =
        QuotientGroup.mk ⟨k * x * k⁻¹, hkx⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact hfix k hk
    have h4 := h1.symm.trans ((congrArg φ h3).trans h2)
    rw [QuotientGroup.eq, mem_subgroupOf] at h4
    exact h4
  have h5 : φ (QuotientGroup.mk ⟨x, hx⟩) = 1 := by
    rw [hφ ⟨x, hx⟩ ⟨w, hw⟩ hxw, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hwY
  exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 ((MulEquiv.map_eq_one_iff φ).1 h5))

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
