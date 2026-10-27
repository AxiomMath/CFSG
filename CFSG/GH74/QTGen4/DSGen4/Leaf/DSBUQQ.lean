module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBUQQ

variable {G : Type} [Group G]

def cj (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g : G} {K : Subgroup G} {x : G} : x ∈ cj g K ↔ g⁻¹ * x * g ∈ K := by
  unfold cj
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_mul (g h : G) (K : Subgroup G) : cj (g * h) K = cj g (cj h K) := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

theorem cj_one (K : Subgroup G) : cj 1 K = K := by
  ext x
  rw [mem_cj]
  simp

theorem cj_inv_cancel (g : G) (K : Subgroup G) : cj g⁻¹ (cj g K) = K := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_inf (g : G) (K M : Subgroup G) : cj g (K ⊓ M) = cj g K ⊓ cj g M := by
  ext x
  simp only [mem_cj, Subgroup.mem_inf]

theorem card_cj (g : G) (K : Subgroup G) : Nat.card (cj g K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem relIndex_cj (g : G) (H K : Subgroup G) : (cj g H).relIndex (cj g K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective H K (MulAut.conj g).injective

theorem cj_eq_self_of_mem_normalizer {g : G} {K : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : cj g K = K := by
  ext x
  rw [mem_cj]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) x
  rw [inv_inv] at this
  exact this.symm

theorem relIndex_inf_eq_relIndex_sup [Finite G] {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    (H ⊓ K).relIndex H = K.relIndex (H ⊔ K) := by
  have hsub : (H ⊓ K).subgroupOf H = K.subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  unfold Subgroup.relIndex
  rw [hsub]
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer h
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K h).toEquiv

theorem comm_closure {k : Set G} {Z : Subgroup G}
    (hcZ : ∀ a ∈ k, ∀ z ∈ Z, a * z = z * a)
    (hk : ∀ a ∈ k, ∀ b ∈ k, ⁅a, b⁆ ∈ Z) :
    ∀ x ∈ Subgroup.closure k, ∀ y ∈ Subgroup.closure k, ⁅x, y⁆ ∈ Z := by
  have hcen : Subgroup.closure k ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (hcZ a ha z hz).symm
  have hcen' : ∀ u ∈ Subgroup.closure k, ∀ z ∈ Z, u * z = z * u := by
    intro u hu z hz
    exact (Subgroup.mem_centralizer_iff.mp (hcen hu)) z hz |>.symm
  have step1 : ∀ a ∈ k, ∀ y ∈ Subgroup.closure k, ⁅a, y⁆ ∈ Z := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hk a ha x hx
    | one => simp
    | mul x z hx hz ihx ihz =>
      have e : ⁅a, x * z⁆ = ⁅a, x⁆ * (x * ⁅a, z⁆ * x⁻¹) := by group
      rw [e]
      refine Z.mul_mem ihx ?_
      have hc := hcen' x hx _ ihz
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact ihz
    | inv x hx ihx =>
      have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x := by group
      rw [e]
      have hc := hcen' x⁻¹ (Subgroup.inv_mem _ hx) _ (Z.inv_mem ihx)
      rw [hc, mul_assoc, inv_mul_cancel, mul_one]
      exact Z.inv_mem ihx
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact fun y hy => step1 a ha y hy
  | one => intro y _; simp
  | mul a b ha hb iha ihb =>
    intro y hy
    have e : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by group
    rw [e]
    refine Z.mul_mem ?_ (iha y hy)
    have hc := hcen' a ha _ (ihb y hy)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact ihb y hy
  | inv a ha iha =>
    intro y hy
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by group
    rw [e]
    have hc := hcen' a⁻¹ (Subgroup.inv_mem _ ha) _ (Z.inv_mem (iha y hy))
    rw [hc, mul_assoc, inv_mul_cancel, mul_one]
    exact Z.inv_mem (iha y hy)

theorem central_closure {k : Set G} {Z : Subgroup G}
    (hcZ : ∀ a ∈ k, ∀ z ∈ Z, a * z = z * a) :
    ∀ u ∈ Subgroup.closure k, ∀ z ∈ Z, u * z = z * u := by
  have hcen : Subgroup.closure k ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (hcZ a ha z hz).symm
  intro u hu z hz
  exact (Subgroup.mem_centralizer_iff.mp (hcen hu)) z hz |>.symm

theorem sq_closure {k : Set G} {Z : Subgroup G}
    (hcZ : ∀ a ∈ k, ∀ z ∈ Z, a * z = z * a)
    (hk : ∀ a ∈ k, ∀ b ∈ k, ⁅a, b⁆ ∈ Z) (hsq : ∀ a ∈ k, a ^ 2 ∈ Z) :
    ∀ x ∈ Subgroup.closure k, x ^ 2 ∈ Z := by
  have hcomm := comm_closure hcZ hk
  have hcen := central_closure hcZ
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact hsq a ha
  | one => simp
  | mul a b ha hb iha ihb =>
    have hc : ⁅b, a⁆ ∈ Z := hcomm b hb a ha
    have hyx : b * a = ⁅b, a⁆ * a * b := by
      rw [commutatorElement_def]; group
    have hac : a * ⁅b, a⁆ = ⁅b, a⁆ * a := hcen a ha _ hc
    have e : (a * b) ^ 2 = ⁅b, a⁆ * a ^ 2 * b ^ 2 := by
      rw [sq, sq, sq]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (⁅b, a⁆ * a * b) * b := by rw [hyx]
        _ = (a * ⁅b, a⁆) * a * (b * b) := by group
        _ = (⁅b, a⁆ * a) * a * (b * b) := by rw [hac]
        _ = ⁅b, a⁆ * (a * a) * (b * b) := by group
    rw [e]
    exact Z.mul_mem (Z.mul_mem hc iha) ihb
  | inv a ha iha =>
    rw [inv_pow]
    exact Z.inv_mem iha

theorem relIndex_le_of_comm_sq [Finite G]
    (hR : ∀ R : Subgroup G, IsPGroup 2 R → (dsFrattini R).relIndex R ≤ 16)
    {U Z : Subgroup G} (hU : IsPGroup 2 U)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ Z) (hsq : ∀ x ∈ U, x ^ 2 ∈ Z) :
    Z.relIndex U ≤ 16 := by
  have hΦ : dsFrattini U ≤ Z := by
    unfold dsFrattini
    apply CFSG.Quasithin.frattini_map_le_of_forall hU
    · intro x hx y hy
      rw [← commutatorElement_def]
      exact hcomm x hx y hy
    · exact hsq
  have hne : (dsFrattini U).relIndex U ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  exact (Subgroup.relIndex_le_of_le_left hΦ hne).trans (hR U hU)

theorem card_le_of_relIndex {U Z : Subgroup G} (hZU : Z ≤ U) (hZ : Nat.card Z = 4)
    (h16 : Z.relIndex U ≤ 16) : Nat.card U ≤ 64 := by
  have h : Z.relIndex U * Nat.card (Z ⊓ U : Subgroup G) = Nat.card U :=
    Subgroup.relIndex_mul_card Z U
  rw [inf_eq_left.mpr hZU, hZ] at h
  rw [← h]
  omega

theorem perm3_facts : (finRotate 3) ^ 3 = 1 ∧ (finRotate 3) ≠ 1 ∧
    (finRotate 3) ^ 2 ≠ 1 ∧ (finRotate 3) ^ 4 ≠ 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem card_perm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem exists_s3_elt [Finite G] {L1 L2 S : Subgroup G}
    (hs3 : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hO : pCoreOf 2 L2 ≤ S) (hS2 : IsPGroup 2 S)
    (hlt : borelOf L2 S < L2) (hBL : L2 ⊓ bigB L1 L2 S = borelOf L2 S) :
    ∃ d ∈ L2, d ∉ bigB L1 L2 S ∧ d ^ 2 ∉ bigB L1 L2 S := by
  obtain ⟨e⟩ := hs3
  set P : Subgroup ↥L2 := CFSG.Open.pCore 2 ↥L2 with hP
  let q : ↥L2 →* (↥L2 ⧸ P) := QuotientGroup.mk' P
  let φ : ↥L2 →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp q
  have hφs : Function.Surjective φ := by
    intro g
    obtain ⟨x, hx⟩ := e.surjective g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P x
    exact ⟨y, hx⟩
  have hker : ∀ x : ↥L2, φ x = 1 ↔ x ∈ P := fun x => by
    simp only [φ, q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  set B2 : Subgroup ↥L2 := (borelOf L2 S).subgroupOf L2 with hB2
  have hmemB2 : ∀ x : ↥L2, x ∈ B2 ↔ (x : G) ∈ borelOf L2 S := fun x => Iff.rfl
  have hSL : S ⊓ L2 ≤ borelOf L2 S := by
    unfold borelOf
    exact le_inf inf_le_right Subgroup.le_normalizer
  have hkerB : ∀ x : ↥L2, φ x = 1 → x ∈ B2 := by
    intro x hx
    rw [hker] at hx
    have hx' : (x : G) ∈ pCoreOf 2 L2 := Subgroup.mem_map_of_mem _ hx
    exact (hmemB2 x).mpr (hSL (Subgroup.mem_inf.mpr ⟨hO hx', x.2⟩))
  set H : Subgroup (Equiv.Perm (Fin 3)) := B2.map φ with hH
  have hkerle : φ.ker ≤ B2 := fun x hx => hkerB x hx
  have hHtop : H ≠ ⊤ := by
    intro htop
    have h1 : (B2.map φ).comap φ = B2 ⊔ φ.ker := Subgroup.comap_map_eq φ B2
    rw [← hH, htop, Subgroup.comap_top] at h1
    have htop2 : (⊤ : Subgroup ↥L2) ≤ B2 := by
      rw [h1]
      exact sup_le le_rfl hkerle
    have hL2 : L2 ≤ borelOf L2 S := by
      intro x hx
      exact (hmemB2 ⟨x, hx⟩).mp (htop2 (Subgroup.mem_top _))
    exact (not_le_of_gt hlt) hL2
  have htex : ∃ t : ↥L2, (t : G) ∈ S ∧ φ t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊓ L2 ≤ pCoreOf 2 L2 := by
      intro x hx
      obtain ⟨hxS, hxL⟩ := hx
      have h1 := (hker ⟨x, hxL⟩).mp (hcon ⟨x, hxL⟩ hxS)
      exact Subgroup.mem_map_of_mem _ h1
    have heq : S ⊓ L2 = pCoreOf 2 L2 :=
      le_antisymm hsub (le_inf hO (CFSG.LieType.BorelTits.pCoreOf_le 2 L2))
    have hN : L2 ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
      rw [heq]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L2
    have hbor : borelOf L2 S = L2 := by
      unfold borelOf
      exact inf_eq_left.mpr hN
    exact (ne_of_lt hlt) hbor
  obtain ⟨t, htS, htne⟩ := htex
  have htB2 : t ∈ B2 := (hmemB2 t).mpr (hSL (Subgroup.mem_inf.mpr ⟨htS, t.2⟩))
  have htH : φ t ∈ H := Subgroup.mem_map_of_mem φ htB2
  obtain ⟨k, hk⟩ := hS2 ⟨(t : G), htS⟩
  have hk' : t ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hφk : φ t ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
  have hord : orderOf (φ t) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hφk
  obtain ⟨j, _, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have h2 : 2 ∣ orderOf (φ t) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · exfalso
      apply htne
      apply orderOf_eq_one_iff.mp
      rw [hjeq, hj0, pow_zero]
    · rw [hjeq]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hjpos)
  have h2H : 2 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨φ t, htH⟩ : H)
    rw [Subgroup.orderOf_mk] at this
    exact h2.trans this
  have hdvd6 : Nat.card H ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [card_perm3] at this
  have hne6 : Nat.card H ≠ 6 := by
    intro h6
    apply hHtop
    exact Subgroup.eq_top_of_card_eq H (by rw [h6, card_perm3])
  have hcard2 : Nat.card H = 2 := by
    have hmem : Nat.card H ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hdvd6, by norm_num⟩
    have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> omega
  have hc2 : ∀ x ∈ H, x ^ 2 = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := ↥H) (x := ⟨x, hx⟩)
    rw [hcard2] at this
    simpa using congrArg Subtype.val this
  obtain ⟨d', hd'⟩ := hφs (finRotate 3)
  refine ⟨(d' : G), d'.2, ?_, ?_⟩
  · intro hdB
    have hmem' : (d' : G) ∈ borelOf L2 S := by
      rw [← hBL]
      exact ⟨d'.2, hdB⟩
    have hd'B2 : d' ∈ B2 := (hmemB2 d').mpr hmem'
    have hmem : finRotate 3 ∈ H := by
      rw [← hd']
      exact Subgroup.mem_map_of_mem φ hd'B2
    exact perm3_facts.2.2.1 (hc2 _ hmem)
  · intro hdB
    have hmem' : ((d' ^ 2 : ↥L2) : G) ∈ borelOf L2 S := by
      rw [← hBL]
      exact ⟨(d' ^ 2 : ↥L2).2, by simpa using hdB⟩
    have hd2B2 : d' ^ 2 ∈ B2 := (hmemB2 _).mpr hmem'
    have hmem : (finRotate 3) ^ 2 ∈ H := by
      rw [← hd', ← map_pow]
      exact Subgroup.mem_map_of_mem φ hd2B2
    have h4 := hc2 _ hmem
    rw [← pow_mul] at h4
    exact perm3_facts.2.2.2 (by simpa using h4)

theorem comm_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (isMulCommutative_iff.1 hE.1 ⟨a, ha⟩ ⟨b, hb⟩)

theorem sq_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {a : G} (ha : a ∈ E) :
    a ^ 2 = 1 :=
  hE.2 a ha

theorem cj_commute {E : Subgroup G} (hE : IsElemAbelian 2 E) (u : G) {a b : G}
    (ha : a ∈ cj u E) (hb : b ∈ cj u E) : a * b = b * a := by
  rw [mem_cj] at ha hb
  have h := comm_of_elemAbelian hE ha hb
  calc a * b = u * ((u⁻¹ * a * u) * (u⁻¹ * b * u)) * u⁻¹ := by group
    _ = u * ((u⁻¹ * b * u) * (u⁻¹ * a * u)) * u⁻¹ := by rw [h]
    _ = b * a := by group

theorem sq_cj {E : Subgroup G} (hE : IsElemAbelian 2 E) (u : G) {a : G} (ha : a ∈ cj u E) :
    a ^ 2 = 1 := by
  rw [mem_cj] at ha
  have h := sq_of_elemAbelian hE ha
  have e2 : (u⁻¹ * a * u) ^ 2 = u⁻¹ * a ^ 2 * u := by
    simp only [sq]; group
  rw [e2] at h
  calc a ^ 2 = u * (u⁻¹ * a ^ 2 * u) * u⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem not_comm_cj [Finite G] {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S)
    (hrk2 : ∀ R : Subgroup G, IsElemAbelian 2 R → Nat.card R ≤ 16)
    {E : Subgroup G} (hEel : IsElemAbelian 2 E) (hEcard : Nat.card E = 16)
    (hEP : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (E : Set G))
    (hEle : E ≤ L1 ⊔ L2 ⊔ S) (hE2 : IsPGroup 2 E)
    {w : G} (hwP : w ∈ L2 ⊔ bigB L1 L2 S) (hwB : w ∉ bigB L1 L2 S) :
    ¬ ∀ e ∈ E, ∀ x ∈ cj w E, e * x = x * e := by
  intro hcomm
  have hXcomm : ∀ a ∈ cj w E, ∀ b ∈ cj w E, a * b = b * a := fun a ha b hb =>
    cj_commute hEel w ha hb
  have hk : ∀ a ∈ (E : Set G) ∪ cj w E, ∀ b ∈ (E : Set G) ∪ cj w E,
      ⁅a, b⁆ ∈ (⊥ : Subgroup G) := by
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact comm_of_elemAbelian hEel ha hb
    · exact hcomm a ha b hb
    · exact (hcomm b hb a ha).symm
    · exact hXcomm a ha b hb
  have hcZ : ∀ a ∈ (E : Set G) ∪ cj w E, ∀ z ∈ (⊥ : Subgroup G), a * z = z * a := by
    intro a _ z hz
    rw [Subgroup.mem_bot.mp hz]
    simp
  have hcomm_cl := comm_closure hcZ hk
  have hsq_gen : ∀ a ∈ (E : Set G) ∪ cj w E, a ^ 2 ∈ (⊥ : Subgroup G) := by
    intro a ha
    rw [Subgroup.mem_bot]
    rcases ha with ha | ha
    · exact sq_of_elemAbelian hEel ha
    · exact sq_cj hEel w ha
  have hsq_cl := sq_closure hcZ hk hsq_gen
  set W := Subgroup.closure ((E : Set G) ∪ cj w E) with hW
  have hWel : IsElemAbelian 2 W := by
    refine ⟨isMulCommutative_iff.2 fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · have := hcomm_cl a a.2 b b.2
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · have := hsq_cl x hx
      rwa [Subgroup.mem_bot] at this
  have hEW : E ≤ W := fun e he => Subgroup.subset_closure (Or.inl he)
  have hWcard : Nat.card W ≤ 16 := hrk2 W hWel
  have hEeq : E = W := Subgroup.eq_of_le_of_card_ge hEW (by omega)
  have hXE : cj w E ≤ E := fun x hx => by
    have hxW : x ∈ W := Subgroup.subset_closure (Or.inr hx)
    rw [hEeq]
    exact hxW
  have hXEq : cj w E = E := Subgroup.eq_of_le_of_card_ge hXE (by rw [card_cj, hEcard])
  have hconj : ∀ x : G, w * x * w⁻¹ ∈ cj w E ↔ x ∈ E := by
    intro x
    rw [mem_cj]
    have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
    rw [e]
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := (hconj x).mpr hx
      rw [hXEq] at h1
      exact h1
    · intro hx
      rw [← hXEq] at hx
      exact (hconj x).mp hx
  have hnorm := normalizer_inf_eq_bigB h hE2 hEle (by
    intro h0
    rw [h0, Subgroup.card_bot] at hEcard
    norm_num at hEcard) hEP
  have hw' : w ∈ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (E : Set G) := ⟨hwP, hwN⟩
  rw [hnorm] at hw'
  exact hwB hw'

theorem cj_centralizer_of_normalizes {S : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (S : Set G)) :
    cj b (Subgroup.centralizer (S : Set G)) = Subgroup.centralizer (S : Set G) := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have hbi : b⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hb
  constructor
  · intro hx s hs
    have hs' := (Subgroup.mem_normalizer_iff.mp hbi s).mp hs
    rw [inv_inv] at hs'
    have := hx _ hs'
    calc s * x = b * (b⁻¹ * s * b * (b⁻¹ * x * b)) * b⁻¹ := by group
      _ = b * (b⁻¹ * x * b * (b⁻¹ * s * b)) * b⁻¹ := by rw [this]
      _ = x * s := by group
  · intro hx s hs
    have hs' := (Subgroup.mem_normalizer_iff.mp hb s).mp hs
    have := hx _ hs'
    calc s * (b⁻¹ * x * b) = b⁻¹ * (b * s * b⁻¹ * x) * b := by group
      _ = b⁻¹ * (x * (b * s * b⁻¹)) * b := by rw [this]
      _ = b⁻¹ * x * b * s := by group

theorem comm_mem_inf {E X : Subgroup G} (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hXE : X ≤ Subgroup.normalizer (E : Set G)) {a b : G} (ha : a ∈ E) (hb : b ∈ X) :
    ⁅a, b⁆ ∈ E ⊓ X := by
  constructor
  · have e1 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [e1]
    refine E.mul_mem ha ?_
    exact (Subgroup.mem_normalizer_iff.mp (hXE hb) a⁻¹).mp (E.inv_mem ha)
  · have e2 : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by rw [commutatorElement_def]
    rw [e2]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEX ha) b).mp hb) (X.inv_mem hb)

theorem cj_mono (g : G) {K M : Subgroup G} (h : K ≤ M) : cj g K ≤ cj g M :=
  Subgroup.map_mono h

theorem num_aux (r0 rel m N : ℕ) (h1 : r0 * m = 16) (h2 : N = r0 * 16) (h3 : N = rel * m)
    (h4 : rel ≤ 16) : 4 ≤ m := by
  have h5 : rel * m ≤ 16 * m := Nat.mul_le_mul_right m h4
  have h6 : r0 ≤ m := by nlinarith
  have h7 : r0 * m ≤ m * m := Nat.mul_le_mul_right m h6
  nlinarith

theorem caseC [Finite G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S)
    {E Z0 : Subgroup G} [DSLeaf LeafM3] [DSLeaf LeafM4]
    (hrk : ∀ R : Subgroup G, IsPGroup 2 R → (dsFrattini R).relIndex R ≤ 16)
    (hrk2 : ∀ R : Subgroup G, IsElemAbelian 2 R → Nat.card R ≤ 16)
    (hSL1 : S ≤ L1) (hsylS : IsSylowTwoOf S L1)
    (hQ1S : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S)
    (hQ2S : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ S)
    (hQ1idx : (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex S = 4)
    (hA5 : A5Chief (L1 ⊔ bigB L1 L2 S) L1 E ⊥)
    (hEel : IsElemAbelian 2 E) (hEQ1 : E ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
    (hZ0 : Z0 = E ⊓ Subgroup.centralizer (S : Set G))
    (hzc : ∀ x ∈ L1 ⊔ bigB L1 L2 S, IsPGroup 2 (Subgroup.zpowers x) →
      (∀ e ∈ E, ⁅x, e⁆ = 1) → x ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
    (hbru : ∀ s ∈ L2 ⊔ bigB L1 L2 S, s ∉ bigB L1 L2 S → ∀ g ∈ L2 ⊔ bigB L1 L2 S,
      g ∈ bigB L1 L2 S ∨ ∃ b₁ ∈ bigB L1 L2 S, ∃ b₂ ∈ bigB L1 L2 S, g = b₁ * s * b₂)
    (hd : ∃ d ∈ L2, d ∉ bigB L1 L2 S ∧ d ^ 2 ∉ bigB L1 L2 S)
    (hc : E ≤ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) : False := by
  have hBS : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := h.bnorm
  have hP1E : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (E : Set G) := hA5.norm_E
  have hP2Q2 : L2 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hP1Q1 : L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hBP1 : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hL1P1 : L1 ≤ L1 ⊔ bigB L1 L2 S := le_sup_left
  have hSP1 : S ≤ L1 ⊔ bigB L1 L2 S := hSL1.trans hL1P1
  have hES : E ≤ S := hEQ1.trans hQ1S
  have hE2 : IsPGroup 2 E := IsPGroup.to_le hsylS.2.1 hES
  have hEle : E ≤ L1 ⊔ L2 ⊔ S := hES.trans le_sup_right
  have hEcard : Nat.card E = 16 := by
    have := hA5.card
    rwa [Subgroup.relIndex_bot_left] at this
  have hQ1cent : ∀ q ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S), ∀ e ∈ E, q * e = e * q := by
    intro q hq e he
    have h1 := hA5.core q hq e he
    rw [Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hQ2P2 : ∀ w ∈ L2 ⊔ bigB L1 L2 S,
      cj w (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) :=
    fun w hw => cj_eq_self_of_mem_normalizer (hP2Q2 hw)
  have hcjQ2 : ∀ w ∈ L2 ⊔ bigB L1 L2 S, cj w E ≤ S := fun w hw =>
    ((cj_mono w hc).trans (le_of_eq (hQ2P2 w hw))).trans hQ2S
  have hEN : ∀ w ∈ L2 ⊔ bigB L1 L2 S,
      E ≤ Subgroup.normalizer ((cj w E : Subgroup G) : Set G) := by
    intro w hw e he
    have hpQ : w⁻¹ * e * w ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
      rw [← hQ2P2 w⁻¹ (Subgroup.inv_mem _ hw), mem_cj, inv_inv]
      have e1 : w * (w⁻¹ * e * w) * w⁻¹ = e := by group
      rw [e1]
      exact hc he
    have hpN : w⁻¹ * e * w ∈ Subgroup.normalizer (E : Set G) :=
      hP1E (hL1P1 (hSL1 (hQ2S hpQ)))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_cj, mem_cj]
    have e2 : w⁻¹ * (e * x * e⁻¹) * w =
        (w⁻¹ * e * w) * (w⁻¹ * x * w) * (w⁻¹ * e * w)⁻¹ := by group
    rw [e2]
    exact Subgroup.mem_normalizer_iff.mp hpN (w⁻¹ * x * w)
  have hcjNE : ∀ w ∈ L2 ⊔ bigB L1 L2 S, cj w E ≤ Subgroup.normalizer (E : Set G) := fun w hw x hx =>
    hP1E (hSP1 (hcjQ2 w hw hx))
  have hnc : ∀ w ∈ L2 ⊔ bigB L1 L2 S, w ∉ bigB L1 L2 S →
      ¬ cj w E ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
    intro w hw hwB hle
    apply not_comm_cj h.hyp hrk2 hEel hEcard hP1E hEle hE2 hw hwB
    intro e he x hx
    exact (hQ1cent x (hle hx) e he).symm
  obtain ⟨d, hdL2, hdB, hd2B⟩ := hd
  have hdP2 : d ∈ L2 ⊔ bigB L1 L2 S := (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S) hdL2
  have hdinvP2 : d⁻¹ ∈ L2 ⊔ bigB L1 L2 S := Subgroup.inv_mem _ hdP2
  have hdinvB : d⁻¹ ∉ bigB L1 L2 S := fun hh => hdB (by simpa using Subgroup.inv_mem _ hh)
  have hnd := hnc d hdP2 hdB
  have hnd' := hnc d⁻¹ hdinvP2 hdinvB
  obtain ⟨y, hyP2, hyB, hyQ1, hor⟩ : ∃ y ∈ L2 ⊔ bigB L1 L2 S, y ∉ bigB L1 L2 S ∧
      ¬ cj y E ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ∧
      (cj y⁻¹ E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex (cj y⁻¹ E) ≤
        (cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex (cj y E) := by
    by_cases hle : (cj d⁻¹ E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex (cj d⁻¹ E) ≤
        (cj d E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex (cj d E)
    · exact ⟨d, hdP2, hdB, hnd, hle⟩
    · refine ⟨d⁻¹, hdinvP2, hdinvB, hnd', ?_⟩
      rw [inv_inv]
      exact (not_le.mp hle).le
  obtain ⟨z, hzP2, hzB, hzy⟩ : ∃ z ∈ L2 ⊔ bigB L1 L2 S, z ∉ bigB L1 L2 S ∧
      ∀ b ∈ bigB L1 L2 S, z ≠ y * b := by
    by_cases hdy : ∃ b ∈ bigB L1 L2 S, d = y * b
    · obtain ⟨b0, hb0, hdb⟩ := hdy
      refine ⟨d ^ 2, Subgroup.pow_mem _ hdP2 2, hd2B, ?_⟩
      intro b hb hz
      apply hdB
      have hy : y * b = d * (b0⁻¹ * b) := by rw [hdb]; group
      have h1 : d * d = d * (b0⁻¹ * b) := by rw [← hy, ← sq, hz]
      rw [mul_left_cancel h1]
      exact (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hb0) hb
    · push Not at hdy
      exact ⟨d, hdP2, hdB, fun b hb hz => hdy b hb hz⟩
  have hXS : cj y E ≤ S := hcjQ2 y hyP2
  have hXN : E ≤ Subgroup.normalizer ((cj y E : Subgroup G) : Set G) := hEN y hyP2
  have hcommy := not_comm_cj h.hyp hrk2 hEel hEcard hP1E hEle hE2 hyP2 hyB
  have hXcomm : ∀ a ∈ cj y E, ∀ b ∈ cj y E, a * b = b * a := fun a ha b hb =>
    cj_commute hEel y ha hb
  have hcomm_sub : ⁅E, cj y E⁆ ≤ cj y E := by
    rw [Subgroup.commutator_le]
    intro e he x hx
    rw [commutatorElement_def]
    exact (cj y E).mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN he) x).mp hx)
      ((cj y E).inv_mem hx)
  have hq : ⁅⁅E, cj y E⁆, cj y E⁆ ≤ (⊥ : Subgroup G) := by
    rw [Subgroup.commutator_le]
    intro c hc x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hXcomm c (hcomm_sub hc) x hx
  have hnt : ¬ ⁅E, cj y E⁆ ≤ (⊥ : Subgroup G) := by
    intro hle
    apply hcommy
    intro e he x hx
    have := hle (Subgroup.commutator_mem_commutator he hx)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hfaith : ∀ x ∈ cj y E, (∀ e ∈ E, ⁅x, e⁆ ∈ (⊥ : Subgroup G)) →
      x ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
    intro x hx hxe
    apply hzc x (hSP1 (hXS hx))
    · exact IsPGroup.to_le hsylS.2.1 (Subgroup.zpowers_le.mpr (hXS hx))
    · intro e he
      exact Subgroup.mem_bot.mp (hxe e he)
  have hYdef : E ⊓ Subgroup.centralizer ((cj y E : Subgroup G) : Set G) ≤ E := inf_le_left
  have hYc : ∀ y' ∈ E ⊓ Subgroup.centralizer ((cj y E : Subgroup G) : Set G),
      ∀ x ∈ cj y E, ⁅y', x⁆ ∈ (⊥ : Subgroup G) := by
    intro y' hy' x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy').2) x hx).symm
  have hcard : (E ⊓ Subgroup.centralizer ((cj y E : Subgroup G) : Set G)).relIndex E ≤
      (cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex (cj y E) := by
    have hsub : E ⊓ cj y (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≤
        E ⊓ Subgroup.centralizer ((cj y E : Subgroup G) : Set G) := by
      intro x hx
      obtain ⟨hxE, hxQ⟩ := hx
      refine Subgroup.mem_inf.mpr ⟨hxE, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h1 := hQ1cent (y⁻¹ * x * y) (mem_cj.mp hxQ) (y⁻¹ * t * y) (mem_cj.mp ht)
      calc t * x = y * ((y⁻¹ * t * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * x * y) * (y⁻¹ * t * y)) * y⁻¹ := by rw [← h1]
        _ = x * t := by group
    have hne : (E ⊓ cj y (pCoreOf 2 (L1 ⊔ bigB L1 L2 S))).relIndex E ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    have h1 := Subgroup.relIndex_le_of_le_left hsub hne
    have h2 : (E ⊓ cj y (pCoreOf 2 (L1 ⊔ bigB L1 L2 S))).relIndex E =
        (cj y⁻¹ E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex (cj y⁻¹ E) := by
      have e1 : cj y⁻¹ (E ⊓ cj y (pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) =
          cj y⁻¹ E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
        rw [cj_inf, cj_inv_cancel]
      rw [← e1, relIndex_cj]
    exact h1.trans (h2.trans_le hor)
  obtain ⟨hNatX, hXQ, hYidx⟩ := m4 hA5 hsylS (hXS.trans le_sup_left) hq hnt hfaith bot_le
    hYdef hYc hcard
  have hXQS : cj y E ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = S := hXQ.trans (sup_eq_left.mpr hQ1S)
  obtain ⟨-, hrel, hcen, hcap, hlast⟩ := (m3 hA5 hsylS).1 hNatX
  have hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (E : Set G) := fun s hs => hP1E (hSP1 hs)
  have hcEE : ⁅E, S⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he s hs
    rw [commutatorElement_def]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hSN s hs) e⁻¹).mp (E.inv_mem he)
    have e1 : e * s * e⁻¹ * s⁻¹ = e * (s * e⁻¹ * s⁻¹) := by group
    rw [e1]
    exact E.mul_mem he h1
  have hZeq : Z0 = ⁅E, S⁆ ⊔ (⊥ : Subgroup G) := by
    ext x
    rw [hZ0, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hxE, hxS⟩
      apply hcap x hxE
      intro t ht
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hxS t ht).symm
    · intro hx
      rw [sup_bot_eq] at hx
      refine ⟨hcEE hx, fun t ht => ?_⟩
      have := Subgroup.mem_bot.mp (hcen t ht x (by rw [sup_bot_eq]; exact hx))
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
  have hZcard : Nat.card Z0 = 4 := by
    rw [hZeq, ← Subgroup.relIndex_bot_left, hrel]
  have hZ0E : Z0 ≤ E := by rw [hZ0]; exact inf_le_left
  have hZ0S : ∀ x ∈ Z0, ∀ s ∈ S, s * x = x * s := by
    intro x hx
    rw [hZ0, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hx
    exact hx.2
  have hZY : Z0 ≤ E ⊓ Subgroup.centralizer ((cj y E : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hZ0E hx, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    exact hZ0S x hx t (hXS ht)
  have hYZ : E ⊓ Subgroup.centralizer ((cj y E : Subgroup G) : Set G) = Z0 := by
    have h1 := Subgroup.relIndex_mul_card
      (E ⊓ Subgroup.centralizer ((cj y E : Subgroup G) : Set G)) E
    rw [hYidx, hEcard, inf_eq_left.mpr hYdef] at h1
    exact (Subgroup.eq_of_le_of_card_ge hZY (by omega)).symm
  have hEX_le : E ⊓ cj y E ≤ Z0 := by
    rw [← hYZ]
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
      Subgroup.mem_centralizer_iff.mpr fun t ht =>
        (hXcomm x (Subgroup.mem_inf.mp hx).2 t ht).symm⟩
  have hr0 : (E ⊓ cj y E).relIndex E = (cj y E).relIndex (E ⊔ cj y E) :=
    relIndex_inf_eq_relIndex_sup hXN
  have hsupcard : Nat.card ↥(E ⊔ cj y E) = (cj y E).relIndex (E ⊔ cj y E) * 16 := by
    have h1 := Subgroup.relIndex_mul_card (cj y E) (E ⊔ cj y E)
    rw [inf_eq_left.mpr le_sup_right, card_cj, hEcard] at h1
    omega
  have hkZ : ∀ a ∈ (E : Set G) ∪ cj y E, ∀ b ∈ (E : Set G) ∪ cj y E,
      ⁅a, b⁆ ∈ E ⊓ cj y E := by
    intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (comm_of_elemAbelian hEel ha hb)]
      exact (E ⊓ cj y E).one_mem
    · exact comm_mem_inf hXN (hcjNE y hyP2) ha hb
    · have e1 : ⁅a, b⁆ = (⁅b, a⁆)⁻¹ := by simp only [commutatorElement_def]; group
      rw [e1]
      exact (E ⊓ cj y E).inv_mem (comm_mem_inf hXN (hcjNE y hyP2) hb ha)
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hXcomm a ha b hb)]
      exact (E ⊓ cj y E).one_mem
  have hkZsq : ∀ a ∈ (E : Set G) ∪ cj y E, a ^ 2 ∈ E ⊓ cj y E := by
    intro a ha
    rcases ha with ha | ha
    · rw [sq_of_elemAbelian hEel ha]
      exact (E ⊓ cj y E).one_mem
    · rw [sq_cj hEel y ha]
      exact (E ⊓ cj y E).one_mem
  have hkZc : ∀ a ∈ (E : Set G) ∪ cj y E, ∀ z' ∈ E ⊓ cj y E, a * z' = z' * a := by
    intro a ha z' hz'
    rcases ha with ha | ha
    · exact comm_of_elemAbelian hEel ha (Subgroup.mem_inf.mp hz').1
    · exact hXcomm a ha z' (Subgroup.mem_inf.mp hz').2
  have hWeq : Subgroup.closure ((E : Set G) ∪ cj y E) = E ⊔ cj y E := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact (le_sup_left : E ≤ E ⊔ cj y E) hx
      · exact (le_sup_right : cj y E ≤ E ⊔ cj y E) hx
    · exact sup_le (fun e he => Subgroup.subset_closure (Or.inl he))
        (fun x hx => Subgroup.subset_closure (Or.inr hx))
  have hWS : Subgroup.closure ((E : Set G) ∪ cj y E) ≤ S := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact hES hx
    · exact hXS hx
  have hW2 : IsPGroup 2 (Subgroup.closure ((E : Set G) ∪ cj y E)) :=
    IsPGroup.to_le hsylS.2.1 hWS
  have hrelW := relIndex_le_of_comm_sq hrk hW2 (comm_closure hkZc hkZ)
    (sq_closure hkZc hkZ hkZsq)
  have hZW : E ⊓ cj y E ≤ Subgroup.closure ((E : Set G) ∪ cj y E) := by
    rw [hWeq]
    exact inf_le_left.trans le_sup_left
  have hWcard : Nat.card ↥(Subgroup.closure ((E : Set G) ∪ cj y E)) =
      (E ⊓ cj y E).relIndex (Subgroup.closure ((E : Set G) ∪ cj y E)) *
        Nat.card ↥(E ⊓ cj y E) := by
    have h1 := Subgroup.relIndex_mul_card (E ⊓ cj y E)
      (Subgroup.closure ((E : Set G) ∪ cj y E))
    rw [inf_eq_left.mpr hZW] at h1
    exact h1.symm
  have hr0m : (E ⊓ cj y E).relIndex E * Nat.card ↥(E ⊓ cj y E) = 16 := by
    have h1 := Subgroup.relIndex_mul_card (E ⊓ cj y E) E
    rw [inf_eq_left.mpr (inf_le_left : E ⊓ cj y E ≤ E), hEcard] at h1
    exact h1
  have hsupW : Nat.card ↥(E ⊔ cj y E) =
      (E ⊓ cj y E).relIndex (Subgroup.closure ((E : Set G) ∪ cj y E)) *
        Nat.card ↥(E ⊓ cj y E) := by
    rw [← hWeq]
    exact hWcard
  have hZi4 : Nat.card ↥(E ⊓ cj y E) = 4 := by
    have hge := num_aux _ _ _ _ hr0m (by rw [hsupcard, hr0]) hsupW hrelW
    have hle : Nat.card ↥(E ⊓ cj y E) ≤ Nat.card Z0 := Subgroup.card_le_of_le hEX_le
    omega
  have hZi_eq : E ⊓ cj y E = Z0 :=
    Subgroup.eq_of_le_of_card_ge hEX_le (by omega)
  have hr0_4 : (E ⊓ cj y E).relIndex E = 4 := by
    rw [hZi4] at hr0m
    omega
  have hsup64 : Nat.card ↥(E ⊔ cj y E) = 64 := by
    rw [hsupcard, ← hr0, hr0_4]
  have hZ0B : ∀ b ∈ bigB L1 L2 S, cj b Z0 = Z0 := by
    intro b hb
    rw [hZ0, cj_inf, cj_eq_self_of_mem_normalizer (hP1E (hBP1 hb)),
      cj_centralizer_of_normalizes (hBS hb)]
  have htr : ∀ w ∈ L2 ⊔ bigB L1 L2 S, w ∉ bigB L1 L2 S → E ⊓ cj w E = Z0 := by
    intro w hw hwB
    rcases hbru y hyP2 hyB w hw with hB | ⟨b1, hb1, b2, hb2, rfl⟩
    · exact absurd hB hwB
    · have hcj : cj (b1 * y * b2) E = cj b1 (cj y E) := by
        rw [cj_mul, cj_mul, cj_eq_self_of_mem_normalizer (hP1E (hBP1 hb2))]
      rw [hcj]
      calc E ⊓ cj b1 (cj y E) = cj b1 E ⊓ cj b1 (cj y E) := by
            rw [cj_eq_self_of_mem_normalizer (hP1E (hBP1 hb1))]
        _ = cj b1 (E ⊓ cj y E) := (cj_inf _ _ _).symm
        _ = cj b1 Z0 := by rw [hZi_eq]
        _ = Z0 := hZ0B b1 hb1
  have hZ0_in_cj : ∀ u ∈ L2 ⊔ bigB L1 L2 S, Z0 ≤ cj u E := by
    intro u hu
    by_cases hub : u ∈ bigB L1 L2 S
    · rw [cj_eq_self_of_mem_normalizer (hP1E (hBP1 hub))]
      exact hZ0E
    · rw [← htr u hu hub]
      exact inf_le_right
  have hcjZ0 : ∀ w ∈ L2 ⊔ bigB L1 L2 S, cj w Z0 = Z0 := by
    intro w hw
    have hle : Z0 ≤ cj w Z0 := by
      have h1 : Z0 ≤ cj w E := hZ0_in_cj w hw
      have h2 : Z0 ≤ cj (w * y) E := hZ0_in_cj (w * y) ((L2 ⊔ bigB L1 L2 S).mul_mem hw hyP2)
      have h3 : cj w (E ⊓ cj y E) = cj w E ⊓ cj (w * y) E := by
        rw [cj_inf, cj_mul]
      rw [hZi_eq] at h3
      rw [h3]
      exact le_inf h1 h2
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_cj w Z0))).symm
  have hcomm_EZ : ∀ w ∈ L2 ⊔ bigB L1 L2 S, ∀ a ∈ E, ∀ b ∈ cj w E, ⁅a, b⁆ ∈ Z0 := by
    intro w hw a ha b hb
    by_cases hwB : w ∈ bigB L1 L2 S
    · rw [cj_eq_self_of_mem_normalizer (hP1E (hBP1 hwB))] at hb
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (comm_of_elemAbelian hEel ha hb)]
      exact Z0.one_mem
    · rw [← htr w hw hwB]
      exact comm_mem_inf (hEN w hw) (hcjNE w hw) ha hb
  have hcomm_conj : ∀ u ∈ L2 ⊔ bigB L1 L2 S, ∀ v ∈ L2 ⊔ bigB L1 L2 S,
      ∀ a ∈ cj u E, ∀ b ∈ cj v E, ⁅a, b⁆ ∈ Z0 := by
    intro u hu v hv a ha b hb
    have ha0 : u⁻¹ * a * u ∈ E := mem_cj.mp ha
    have hb0 : u⁻¹ * b * u ∈ cj (u⁻¹ * v) E := by
      rw [mem_cj]
      have e1 : (u⁻¹ * v)⁻¹ * (u⁻¹ * b * u) * (u⁻¹ * v) = v⁻¹ * b * v := by group
      rw [e1]
      exact mem_cj.mp hb
    have hc0 := hcomm_EZ (u⁻¹ * v) ((L2 ⊔ bigB L1 L2 S).mul_mem ((L2 ⊔ bigB L1 L2 S).inv_mem hu) hv)
      _ ha0 _ hb0
    have e2 : ⁅a, b⁆ = u * ⁅u⁻¹ * a * u, u⁻¹ * b * u⁆ * u⁻¹ := by
      simp only [commutatorElement_def]; group
    have hmem : u * ⁅u⁻¹ * a * u, u⁻¹ * b * u⁆ * u⁻¹ ∈ cj u Z0 := by
      rw [mem_cj]
      have e3 : u⁻¹ * (u * ⁅u⁻¹ * a * u, u⁻¹ * b * u⁆ * u⁻¹) * u =
          ⁅u⁻¹ * a * u, u⁻¹ * b * u⁆ := by group
      rw [e3]
      exact hc0
    rw [hcjZ0 u hu] at hmem
    rw [e2]
    exact hmem
  have hXT : cj y E ⊓ cj z E = Z0 := by
    have hw : y⁻¹ * z ∈ L2 ⊔ bigB L1 L2 S := (L2 ⊔ bigB L1 L2 S).mul_mem
      ((L2 ⊔ bigB L1 L2 S).inv_mem hyP2) hzP2
    have hwB : y⁻¹ * z ∉ bigB L1 L2 S := fun hh => hzy _ hh (by group)
    have hh := htr (y⁻¹ * z) hw hwB
    calc cj y E ⊓ cj z E = cj y E ⊓ cj (y * (y⁻¹ * z)) E := by rw [mul_inv_cancel_left]
      _ = cj y (E ⊓ cj (y⁻¹ * z) E) := by rw [cj_inf, cj_mul]
      _ = cj y Z0 := by rw [hh]
      _ = Z0 := hcjZ0 y hyP2
  have hET : E ⊓ cj z E = Z0 := htr z hzP2 hzB
  have hgen : ∀ a ∈ (E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G),
      ∃ u ∈ L2 ⊔ bigB L1 L2 S, a ∈ cj u E := by
    intro a ha
    rcases ha with (ha | ha) | ha
    · exact ⟨1, (L2 ⊔ bigB L1 L2 S).one_mem, by rw [cj_one]; exact ha⟩
    · exact ⟨y, hyP2, ha⟩
    · exact ⟨z, hzP2, ha⟩
  have hk3 : ∀ a ∈ (E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G),
      ∀ b ∈ (E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G), ⁅a, b⁆ ∈ Z0 := by
    intro a ha b hb
    obtain ⟨u, hu, hau⟩ := hgen a ha
    obtain ⟨v, hv, hbv⟩ := hgen b hb
    exact hcomm_conj u hu v hv a hau b hbv
  have hcZ3 : ∀ a ∈ (E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G),
      ∀ c ∈ Z0, a * c = c * a := by
    intro a ha c hc
    obtain ⟨u, hu, hau⟩ := hgen a ha
    exact cj_commute hEel u hau (hZ0_in_cj u hu hc)
  have hsq3 : ∀ a ∈ (E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G), a ^ 2 ∈ Z0 := by
    intro a ha
    obtain ⟨u, hu, hau⟩ := hgen a ha
    rw [sq_cj hEel u hau]
    exact Z0.one_mem
  have hU3S : Subgroup.closure ((E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G)) ≤ S := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact hES hx
    · exact hXS hx
    · exact hcjQ2 z hzP2 hx
  have hU3_2 : IsPGroup 2
      (Subgroup.closure ((E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G))) :=
    IsPGroup.to_le hsylS.2.1 hU3S
  have hZU3 : Z0 ≤ Subgroup.closure ((E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G)) := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl (Or.inl (hZ0E hx)))
  have hrel3 := relIndex_le_of_comm_sq hrk hU3_2 (comm_closure hcZ3 hk3)
    (sq_closure hcZ3 hk3 hsq3)
  have hcard3 := card_le_of_relIndex hZU3 hZcard hrel3
  have hEXU : E ⊔ cj y E ≤
      Subgroup.closure ((E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G)) :=
    sup_le (fun e he => Subgroup.subset_closure (Or.inl (Or.inl he)))
      (fun x hx => Subgroup.subset_closure (Or.inl (Or.inr hx)))
  have hEXeq : E ⊔ cj y E =
      Subgroup.closure ((E : Set G) ∪ (cj y E : Set G) ∪ (cj z E : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hEXU (by omega)
  have hTsub : cj z E ≤ E ⊔ cj y E := by
    intro t ht
    rw [hEXeq]
    exact Subgroup.subset_closure (Or.inr ht)
  obtain ⟨e'', heT, he''Z⟩ : ∃ e'' ∈ cj z E, e'' ∉ Z0 := by
    by_contra hcon
    push Not at hcon
    have hle : cj z E ≤ Z0 := fun t ht => hcon t ht
    have := Subgroup.card_le_of_le hle
    rw [card_cj, hEcard, hZcard] at this
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (hcjNE y hyP2)).mp (hTsub heT)
  have hsq_e : (a * b) ^ 2 = 1 := by
    rw [← hab]
    exact sq_cj hEel z heT
  have ha2 : a * a = 1 := by rw [← sq]; exact sq_of_elemAbelian hEel ha
  have hb2 : b * b = 1 := by rw [← sq]; exact sq_cj hEel y hb
  have hcom_ab : a * b = b * a := by
    have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq_e)
    have h2 : (a * b)⁻¹ = b * a := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
    exact h1.symm.trans h2
  have hT' : a * b ∈ cj z E := hab ▸ heT
  have haZ : a ∉ Z0 := by
    intro haZ
    apply he''Z
    rw [hab, ← hXT]
    exact Subgroup.mem_inf.mpr ⟨(cj y E).mul_mem (hZ0_in_cj y hyP2 haZ) hb, hT'⟩
  have hbZ : b ∉ Z0 := by
    intro hbZ
    apply he''Z
    rw [hab, ← hET]
    exact Subgroup.mem_inf.mpr ⟨E.mul_mem ha (hZ0E hbZ), hT'⟩
  have hXQN : cj y E ≤ Subgroup.normalizer
      ((pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Subgroup G) : Set G) :=
    fun x hx => hP1Q1 (hSP1 (hXS hx))
  have hXQrel : (cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex (cj y E) = 4 := by
    rw [relIndex_inf_eq_relIndex_sup hXQN, hXQS, hQ1idx]
  have hcardXQ : Nat.card ↥(cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) (cj y E)
    rw [inf_eq_left.mpr (inf_le_left : cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ cj y E),
      hXQrel, card_cj, hEcard] at h1
    omega
  have hZQ : Z0 ≤ cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hZ0_in_cj y hyP2 hx, hEQ1 (hZ0E hx)⟩
  have hXQ1 : cj y E ⊓ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = Z0 :=
    (Subgroup.eq_of_le_of_card_ge hZQ (by omega)).symm
  have hbQ1 : b ∉ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
    intro hbQ
    apply hbZ
    rw [← hXQ1]
    exact Subgroup.mem_inf.mpr ⟨hb, hbQ⟩
  have hbS : b ∈ S ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := (le_sup_left : S ≤ S ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) (hXS hb)
  have haN : a ∉ ⁅E, S⁆ ⊔ (⊥ : Subgroup G) := by
    rw [← hZeq]
    exact haZ
  have hfin := hlast b hbS hbQ1 a ha haN
  exact hfin (Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr hcom_ab))

end DSBUQQ

theorem leafDSBUQQ [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafDSBS3Vertex] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafM3] [DSLeaf LeafM4] [DSLeaf LeafM5] [DSLeaf LeafBruhat] [DSLeaf LeafSylowS] [DSLeaf LeafRankBounds] : LeafDSBUQQ := by
  intro G _ _ L1 L2 S h cU
  have hQ1L1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ L1 := (dsba5_vertex h).2.2
  have hQ1idx : (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex S = 4 := (dsba5_vertex h).2.1
  have hS1eq : S = (S ⊓ L1) ⊔ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := (dsba5_vertex h).1
  have hSL1 : S ≤ L1 := by
    rw [hS1eq]
    exact sup_le inf_le_right hQ1L1
  have hQ2def : dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
    unfold dsQ
    rw [bigB_comm]
  have hQ2S3 : (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)).relIndex S = 2 := by
    rw [← hQ2def]
    exact (dsbs3_vertex h).2.1
  have hQ2card : Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) =
      2 * Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := by
    rw [← hQ2def]
    exact (dsbs3_vertex h).2.2.2
  have hsylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := (sylow_s h.hyp).2.1
  have hQ1S : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := (sylow_s h.hyp).2.2
  have hQ2S : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ S := by
    have := (sylow_s h.hyp.symm).2.2
    rwa [bigB_comm L1 L2 S] at this
  have hsylS : IsSylowTwoOf S L1 := by
    refine ⟨hSL1, hsylP1.2.1, fun h2 => hsylP1.2.2 (h2.trans ?_)⟩
    have := Subgroup.relIndex_mul_relIndex (H := S) (K := L1) (L := L1 ⊔ bigB L1 L2 S)
      hSL1 le_sup_left
    exact Dvd.intro _ this
  have hP1Q1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hP2Q2 : L2 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hP2L2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have := F1.parabolic_le_normalizer h.hyp.symm
    rwa [bigB_comm L1 L2 S] at this
  have hA5par : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) := hA5par.quot
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, h.bnorm⟩
  obtain ⟨hA5, hEΩeq, hZ0eq, hzc⟩ := zi_chief hZS hq1 cU
  obtain ⟨-, -, -, hΩel, -, -, -⟩ := zi_structure hZS
  have hΩQ : dsOmega1 (centerOf (dsQ L1 L2 S)) ≤ dsQ L1 L2 S := by
    unfold dsOmega1
    rw [Subgroup.closure_le]
    intro x hx
    exact (inf_le_left : centerOf (dsQ L1 L2 S) ≤ dsQ L1 L2 S) (show x ∈ centerOf (dsQ L1 L2 S) from hx.1)
  have hEel : IsElemAbelian 2 (dsZi L1 S) := by
    rw [hEΩeq]
    exact hΩel
  have hEQ1 : dsZi L1 S ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
    rw [hEΩeq]
    exact hΩQ
  have hpc : pCoreOf 2 L1 = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) := by
    rw [← F1.inf_pCoreOf_parabolic_eq h.hyp, inf_eq_left.mpr hQ1L1]
  have hBorel : borelOf L1 S = L1 ⊓ Subgroup.normalizer (S : Set G) := by
    unfold borelOf
    rw [inf_eq_left.mpr hSL1]
  have hBP1Q1 : bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S).trans hP1Q1
  have hBP2Q2 : bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S).trans hP2Q2
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer
      ((pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hBP1Q1 hBP2Q2
  have hXN : L1 ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer
      ((pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Subgroup G) : Set G) := by
    intro x hx
    apply hBN
    rw [← hBorel] at hx
    exact (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) hx
  have hQab : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = S := by
    have hm5 := (m5 hq1 hsylS).1 (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊔ pCoreOf 2 (L2 ⊔ bigB L1 L2 S))
      ((le_of_eq hpc).trans le_sup_left) (sup_le hQ1S hQ2S) hXN
    rcases hm5 with hm5 | hm5
    · exfalso
      have hQ2le : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
        (le_sup_right : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ _).trans (hm5.le.trans hpc.le)
      have h1 := Subgroup.card_le_of_le hQ2le
      have h2 : 0 < Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) := Nat.card_pos
      omega
    · exact hm5
  have hSP2 : S ≤ L2 ⊔ bigB L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hQ1NQ2 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤
      Subgroup.normalizer (pCoreOf 2 (L2 ⊔ bigB L1 L2 S) : Set G) := fun x hx =>
    hP2Q2 (hSP2 (hQ1S hx))
  have hb : (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)).relIndex
      (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = 2 := by
    rw [DSBUQQ.relIndex_inf_eq_relIndex_sup hQ1NQ2, hQab, hQ2S3]
  have hrkpair : (∀ R : Subgroup G, IsPGroup 2 R → (dsFrattini R).relIndex R ≤ 16) ∧
      (∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 16) := rank_bounds
  have hO : pCoreOf 2 L2 ≤ S := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsub : pCoreOf 2 L2 ≤ L2 ⊔ bigB L1 L2 S :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L2).trans le_sup_left
    have hN : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer ((pCoreOf 2 L2 : Subgroup G) : Set G) :=
      hP2L2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L2)
    exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hsub hN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L2)).trans hQ2S
  have hlt : borelOf L2 S < L2 := F1.lt_borelOf h.hyp.symm
  have hBL : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
    have := F1.inf_bigB_eq_borelOf h.hyp.symm
    rwa [bigB_comm L1 L2 S] at this
  have hd := DSBUQQ.exists_s3_elt h.s3 hO hsylP1.2.1 hlt hBL
  have hbru := bruhat h.hyp.symm (Or.inr h.s3)
  simp only [bigB_comm L1 L2 S] at hbru
  have hcC : ¬ dsZi L1 S ≤ dsQ L2 L1 S := by
    intro hc
    have hc' : dsZi L1 S ≤ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
      rw [← hQ2def]
      exact hc
    exact DSBUQQ.caseC h hrkpair.1 hrkpair.2 hSL1 hsylS hQ1S hQ2S hQ1idx hA5 hEel hEQ1 hZ0eq
      hzc hbru hd hc'
  refine ⟨?_, ?_, hcC⟩
  · rw [hQ2def]
    exact hQab
  · rw [hQ2def]
    exact hb

end CFSG.GH74.QTGen4.DSGen4
