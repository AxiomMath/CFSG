module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Desc
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Local

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem K0_subgroupOf_normal (n : ℕ) (H : Subgroup X) : ((K0 X n H).subgroupOf H).Normal := by
  have _ := ‹Finite X›
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (K0_le n H)).2 fun c hc => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_K0 n (Subgroup.le_normalizer hc) hy
  · intro hy
    have := conj_mem_K0 n (Subgroup.le_normalizer (H.inv_mem hc)) hy
    simpa [mul_assoc] using this

theorem pPrimeCoreOf_K0_le (n : ℕ) (H : Subgroup X) :
    pPrimeCoreOf 2 (K0 X n H) ≤ pPrimeCoreOf 2 H :=
  pPrimeCoreOf_le_oddCoreOf (K0_le n H) (K0_subgroupOf_normal n H).isSubnormal

theorem IsIntrinsicIn.isPCompIn_K0 {H L : Subgroup X} {u : X} {n : ℕ} (h : IsIntrinsicIn X H L u)
    (hn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) : IsPCompIn 2 (K0 X n H) L := by
  have hLK : L ≤ K0 X n H := le_sSup ⟨⟨u, h⟩, hn⟩
  exact ⟨hLK, isPComponent_subgroupOf_mono hLK (K0_le n H) h.2.2.1.2⟩

theorem aux_K0_comm_mem_of_ne_comm {H L L' : Subgroup X} (hL : IsPCompIn 2 H L)
    (hL' : IsPCompIn 2 H L') (hne : L ≠ L') : ∀ a ∈ L, ∀ b ∈ L', ⁅a, b⁆ ∈ pPrimeCoreOf 2 L := by
  obtain ⟨hLH, hLc⟩ := hL
  obtain ⟨hLH', hLc'⟩ := hL'
  have hne' : L.subgroupOf H ≠ L'.subgroupOf H := fun heq => hne (by
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hLH, inf_of_le_left hLH'] at heq
    exact heq)
  intro a ha b hb
  obtain ⟨-, -, hcomm, -⟩ :=
    (distinct_p_components_core_commutation 2 Nat.prime_two _ _ hLc hLc').2 hne'
  have ha' : (⟨a, hLH ha⟩ : ↥H) ∈ L.subgroupOf H := ha
  have hb' : (⟨b, hLH' hb⟩ : ↥H) ∈ L'.subgroupOf H := hb
  obtain ⟨y, hy, hyc⟩ := (hcomm (Subgroup.commutator_mem_commutator ha' hb')).1
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  have h2 : (pPrimeCore 2 ↥(L.subgroupOf H)).map e.toMonoidHom = pPrimeCore 2 ↥L :=
    pPrimeCore_map_iso 2 e
  have hy' : e y ∈ pPrimeCore 2 ↥L := by
    rw [← h2]
    exact Subgroup.mem_map_of_mem _ hy
  exact ⟨e y, hy', congrArg (fun z : ↥H => (z : X)) hyc⟩

theorem K0_comm_mem_of_ne {H L L' : Subgroup X} {u u' : X} {n : ℕ} (h : IsIntrinsicIn X H L u)
    (hn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) (h' : IsIntrinsicIn X H L' u')
    (hn' : IsDoubleCoverOfAlt (↥L' ⧸ pPrimeCore 2 ↥L') n) (hne : L ≠ L') :
    ∀ a ∈ L, ∀ b ∈ L', ⁅a, b⁆ ∈ pPrimeCoreOf 2 (K0 X n H) := by
  intro a ha b hb
  have hLK := h.isPCompIn_K0 hn
  have hL'K := h'.isPCompIn_K0 hn'
  exact pPrimeCoreOf_le_oddCoreOf hLK.1 (isPComponent_two_iff.1 hLK.2).1
    (aux_K0_comm_mem_of_ne_comm hLK hL'K hne a ha b hb)

theorem IsIntrinsicIn.mem_zStar_K0 {H L : Subgroup X} {u : X} {n : ℕ} (h : IsIntrinsicIn X H L u)
    (hn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) : u ∈ zStar (K0 X n H) := by
  have huL : u ∈ L := h.2.1
  have hLK : L ≤ K0 X n H := le_sSup ⟨⟨u, h⟩, hn⟩
  have huK : u ∈ K0 X n H := hLK huL
  have h9 : IsPCompIn 2 (K0 X n H) L := h.isPCompIn_K0 hn
  have hOL : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 (K0 X n H) :=
    pPrimeCoreOf_le_oddCoreOf h9.1 (isPComponent_two_iff.1 h9.2).1
  refine ⟨huK, Subgroup.le_normalizer huK, mem_normalizer_pPrimeCoreOf_of_mem huK, ?_⟩
  let O : Subgroup X := pPrimeCoreOf 2 (K0 X n H)
  let U : Subgroup X :=
    { carrier := {k | k ∈ normalizer (O : Set X) ∧ ⁅k, u⁆ ∈ O}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨(normalizer (O : Set X)).mul_mem ha1 hb1, ?_⟩
        have e : ⁅a * b, u⁆ = a * ⁅b, u⁆ * a⁻¹ * ⁅a, u⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 ha1 _).1 hb2) ha2
      one_mem' := ⟨(normalizer (O : Set X)).one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨(normalizer (O : Set X)).inv_mem ha1, ?_⟩
        have e : ⁅a⁻¹, u⁆ = a⁻¹ * (⁅a, u⁆)⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.1 ((normalizer (O : Set X)).inv_mem ha1) _).1
          (O.inv_mem ha2)
        rw [inv_inv] at h1
        exact h1 }
  have hsub : K0 X n H ≤ U := by
    refine sSup_le fun L' hL' => ?_
    obtain ⟨⟨u', hu'⟩, hn'⟩ := hL'
    have hLK' : L' ≤ K0 X n H := le_sSup ⟨⟨u', hu'⟩, hn'⟩
    intro a ha
    have haK : a ∈ K0 X n H := hLK' ha
    refine ⟨mem_normalizer_pPrimeCoreOf_of_mem haK, ?_⟩
    by_cases hLL : L' = L
    · rw [hLL] at ha
      exact hOL (h.comm_mem a ha)
    · exact K0_comm_mem_of_ne hu' hn' h hn hLL a ha u huL
  intro k hk
  exact (hsub hk).2

theorem aux_zStar_le_sup_zpowers_center {X : Type} [Group X] {L : Subgroup X} {x : X} (hx : x ∈ L)
    (h : ∀ k ∈ L, ⁅k, x⁆ ∈ pPrimeCoreOf 2 L) :
    (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨m, hm, hmk⟩ := h (k : X) k.2
  have h2 : m = ⁅k, (⟨x, hx⟩ : ↥L)⁆ := Subtype.ext hmk
  have h3 : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⁅k, (⟨x, hx⟩ : ↥L)⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).2 (h2 ▸ hm)
  rw [map_commutatorElement] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

theorem IsIntrinsicIn.zStar_le_sup_zpowers {H L : Subgroup X} {u : X} {n : ℕ}
    (h : IsIntrinsicIn X H L u) (hn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    zStar L ≤ pPrimeCoreOf 2 L ⊔ Subgroup.zpowers u := by
  have hu2 : orderOf u = 2 := h.1
  have huL : u ∈ L := h.2.1
  have hū : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) :=
    aux_zStar_le_sup_zpowers_center huL h.comm_mem
  have hū1 : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ≠ 1 := by
    intro h1
    have h2 : (⟨u, huL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : u ∈ pPrimeCoreOf 2 L := ⟨⟨u, huL⟩, h2, rfl⟩
    have hP : IsPGroup 2 ↥(Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
    have h4 := eq_one_of_mem_pPrimeCoreOf_of_isPGroup h3 hP (Subgroup.mem_zpowers u)
    rw [h4, orderOf_one] at hu2
    omega
  obtain ⟨y, -, huniq⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L))).1 hn.2.1
  intro w hw
  have hwL : w ∈ L := hw.1
  have hwc : (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) :=
    aux_zStar_le_sup_zpowers_center hwL hw.2.2.2
  by_cases h1 : (⟨QuotientGroup.mk (⟨w, hwL⟩ : ↥L), hwc⟩ :
      Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L)) = 1
  · have h2 : (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = 1 :=
      congrArg Subtype.val h1
    have h3 : (⟨w, hwL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 h2
    exact Subgroup.mem_sup_left ⟨⟨w, hwL⟩, h3, rfl⟩
  · have e1 := huniq _ h1
    have e2 := huniq ⟨QuotientGroup.mk (⟨u, huL⟩ : ↥L), hū⟩
      (fun h' => hū1 (congrArg Subtype.val h'))
    have h2 : (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
        QuotientGroup.mk (⟨u, huL⟩ : ↥L) := congrArg Subtype.val (e1.trans e2.symm)
    have h3 : (⟨u, huL⟩ : ↥L)⁻¹ * ⟨w, hwL⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.1 h2.symm
    have h4 : u⁻¹ * w ∈ pPrimeCoreOf 2 L := ⟨_, h3, rfl⟩
    have hweq : w = u * (u⁻¹ * w) := by group
    rw [sup_comm, hweq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers u) h4

theorem mem_sup_center_of_commute_forall {Q : Type*} [Group Q] (S : Finset (Subgroup Q))
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {w : Q}
    (hw : w ∈ S.sup id) (hc : ∀ g ∈ S.sup id, g * w = w * g) :
    w ∈ S.sup (fun A => A ⊓ centralizer (A : Set Q)) := by
  classical
  induction S using Finset.induction_on generalizing w with
  | empty =>
    have hw1 : w = 1 := by simpa using hw
    subst hw1
    simp
  | insert A S' hA ih =>
    have hne : ∀ A' ∈ S', A ≠ A' := fun A' hA' h => hA (by rw [h]; exact hA')
    have hcomm' : ∀ A' ∈ S', ∀ B ∈ S', A' ≠ B → ∀ a ∈ A', ∀ b ∈ B, a * b = b * a :=
      fun A' hA' B hB => hcomm A' (Finset.mem_insert_of_mem hA') B (Finset.mem_insert_of_mem hB)
    have hAA : ∀ A' ∈ S', ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := fun A' hA' =>
      hcomm A (Finset.mem_insert_self A S') A' (Finset.mem_insert_of_mem hA') (hne A' hA')
    have hAB : ∀ a ∈ A, ∀ b ∈ S'.sup id, a * b = b * a :=
      mul_comm_sup_of_forall_mul_comm A S' hAA
    have hsup : (insert A S').sup id = A ⊔ S'.sup id := Finset.sup_insert
    rw [hsup] at hw hc
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_mul_comm hAB hw
    obtain ⟨hA1, hB1⟩ := commute_factors_of_commute_prod hAB ha hb hc
    rw [Finset.sup_insert]
    refine Subgroup.mul_mem_sup ?_ ?_
    · refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hA1 g hg
    · exact ih hcomm' hb hB1

theorem aux_zStar_le_sup_of_sup_eq_top_inf_le {Y : Type} [Group Y] [Finite Y] (A : Subgroup Y) :
    A ⊓ pPrimeCore 2 Y ≤ pPrimeCoreOf 2 A := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : ((A ⊓ pPrimeCore 2 Y).subgroupOf A).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact Subgroup.Normal.subgroupOf inferInstance A
  have hcop : Nat.Coprime 2 (Nat.card ((A ⊓ pPrimeCore 2 Y).subgroupOf A)) := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ pPrimeCore 2 Y ≤ A)).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      pPrimeCore_coprime_card
  have hle : (A ⊓ pPrimeCore 2 Y).subgroupOf A ≤ pPrimeCore 2 ↥A := le_sSup ⟨hnormal, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩

theorem aux_zStar_le_sup_of_sup_eq_top_mem {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    {a : Y} (ha : a ∈ A) (h : ∀ a' ∈ A, ⁅a', a⁆ ∈ pPrimeCore 2 Y) : a ∈ zStar A := by
  refine ⟨ha, Subgroup.le_normalizer ha, mem_normalizer_pPrimeCoreOf_of_mem ha, fun k hk => ?_⟩
  apply aux_zStar_le_sup_of_sup_eq_top_inf_le A
  refine ⟨?_, h k hk⟩
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem hk ha) (A.inv_mem hk)) (A.inv_mem ha)

theorem aux_zStar_le_sup_of_sup_eq_top_map_sup {G H : Type*} [Group G] [Group H] (f : G →* H)
    (S : Finset (Subgroup G)) : (S.sup id).map f = S.sup (fun A => A.map f) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert A S' hA ih =>
    rw [Finset.sup_insert, Finset.sup_insert, Subgroup.map_sup, ih]
    rfl

theorem zStar_le_sup_of_sup_eq_top {Y : Type} [Group Y] [Finite Y] (S : Finset (Subgroup Y))
    (hS : S.sup id = ⊤)
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ pPrimeCore 2 Y) {w : Y}
    (hw : ∀ g : Y, ⁅g, w⁆ ∈ pPrimeCore 2 Y) :
    w ∈ pPrimeCore 2 Y ⊔ S.sup (fun A => zStar A) := by
  classical
  set N : Subgroup Y := pPrimeCore 2 Y with hN
  let q : Y →* Y ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hker : ∀ y : Y, q y = 1 ↔ y ∈ N := fun y => QuotientGroup.eq_one_iff y
  have hcommq : ∀ a b : Y, ⁅a, b⁆ ∈ N → q a * q b = q b * q a := by
    intro a b hab
    have h1 : q ⁅a, b⁆ = 1 := (hker _).2 hab
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  let S' : Finset (Subgroup (Y ⧸ N)) := S.image (Subgroup.map q)
  have hsup : S'.sup id = (S.sup id).map q := by
    rw [aux_zStar_le_sup_of_sup_eq_top_map_sup, Finset.sup_image]
    rfl
  have hS'top : S'.sup id = ⊤ := by
    rw [hsup, hS, Subgroup.map_top, MonoidHom.range_eq_top.2 hq]
  have hcomm' : ∀ A ∈ S', ∀ B ∈ S', A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro Ab hAb Bb hBb hne a ha b hb
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hAb
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hBb
    have hAB : A ≠ B := fun h => hne (by rw [h])
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    exact hcommq a' b' (hcomm A hA B hB hAB a' ha' b' hb')
  have hwc : ∀ g ∈ S'.sup id, g * q w = q w * g := by
    intro g _
    obtain ⟨y, rfl⟩ := hq g
    exact hcommq y w (hw y)
  have hw' : q w ∈ S'.sup id := by rw [hS'top]; exact Subgroup.mem_top _
  have key := mem_sup_center_of_commute_forall S' hcomm' hw' hwc
  have hle : S'.sup (fun Ab => Ab ⊓ centralizer (Ab : Set (Y ⧸ N))) ≤
      (S.sup (fun A => zStar A)).map q := by
    refine Finset.sup_le fun Ab hAb => ?_
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hAb
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx1
    have hza : a ∈ zStar A := by
      refine aux_zStar_le_sup_of_sup_eq_top_mem ha fun a' ha' => ?_
      have h1 : q a' * q a = q a * q a' :=
        Subgroup.mem_centralizer_iff.1 hx2 (q a') ⟨a', ha', rfl⟩
      have h2 : q ⁅a', a⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 h1
      exact (hker _).1 h2
    exact Subgroup.mem_map.2 ⟨a, Finset.le_sup (f := fun A => zStar A) hA hza, rfl⟩
  obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 (hle key)
  have hn : y⁻¹ * w ∈ N := QuotientGroup.eq.1 hyw
  have hweq : w = y * (y⁻¹ * w) := by group
  rw [sup_comm, hweq]
  exact Subgroup.mul_mem_sup hy hn

omit [Finite X] in
theorem aux_zStar_K0_le_sup_pPrimeCoreOf_map {K L : Subgroup X} (hLK : L ≤ K) :
    (pPrimeCoreOf 2 (L.subgroupOf K)).map K.subtype = pPrimeCoreOf 2 L := by
  let e : ↥(L.subgroupOf K) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLK
  have h := pPrimeCore_map_iso 2 e
  unfold pPrimeCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

omit [Finite X] in
theorem aux_zStar_K0_le_sup_zStar_map {K L : Subgroup X} (hLK : L ≤ K) :
    (zStar (L.subgroupOf K)).map K.subtype ≤ zStar L := by
  rintro _ ⟨x, ⟨hxA, -, -, hxc⟩, rfl⟩
  have hxL : (x : X) ∈ L := hxA
  refine ⟨hxL, Subgroup.le_normalizer hxL, mem_normalizer_pPrimeCoreOf_of_mem hxL,
    fun l hl => ?_⟩
  have h := hxc ⟨l, hLK hl⟩ hl
  have h2 := Subgroup.mem_map_of_mem K.subtype h
  rw [aux_zStar_K0_le_sup_pPrimeCoreOf_map hLK] at h2
  exact h2

theorem zStar_K0_le_sup (n : ℕ) (H : Subgroup X) :
    zStar (K0 X n H) ≤ pPrimeCoreOf 2 (K0 X n H) ⊔
      ⨆ (L : Subgroup X) (_ : (∃ u, IsIntrinsicIn X H L u) ∧
          IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n), zStar L := by
  classical
  set K : Subgroup X := K0 X n H with hKdef
  set 𝓘 : Set (Subgroup X) := {L | (∃ u, IsIntrinsicIn X H L u) ∧
      IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n} with h𝓘
  have hK : K = sSup 𝓘 := rfl
  have hLK : ∀ L ∈ 𝓘, L ≤ K := fun L hL => le_sSup hL
  set S0 : Set (Subgroup ↥K) := {A | ∃ L ∈ 𝓘, A = L.subgroupOf K} with hS0def
  have hS0 : S0.Finite := Set.toFinite _
  set S : Finset (Subgroup ↥K) := hS0.toFinset with hSdef
  have hmemS : ∀ A, A ∈ S ↔ ∃ L ∈ 𝓘, A = L.subgroupOf K := fun A => by
    rw [hSdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hSup : S.sup id = ⊤ := by
    rw [Finset.sup_id_eq_sSup, hS0.coe_toFinset]
    refine eq_top_iff.2 ?_
    rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective,
      (Subgroup.gc_map_comap K.subtype).l_sSup]
    have htop : Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := by
      rw [← Subgroup.subgroupOf_self (H := K), Subgroup.map_subgroupOf_eq_of_le le_rfl]
    rw [htop]
    refine hK.le.trans (sSup_le fun L hL => ?_)
    rw [← Subgroup.map_subgroupOf_eq_of_le (hLK L hL)]
    exact le_iSup₂ (f := fun (A : Subgroup ↥K) (_ : A ∈ S0) => Subgroup.map K.subtype A)
      (L.subgroupOf K) ⟨L, hL, rfl⟩
  have hcomm : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ pPrimeCore 2 ↥K := by
    intro A hA B hB hAB a ha b hb
    obtain ⟨L, hL, rfl⟩ := (hmemS A).1 hA
    obtain ⟨L', hL', rfl⟩ := (hmemS B).1 hB
    have hLL' : L ≠ L' := fun h => hAB (by rw [h])
    obtain ⟨⟨u, hu⟩, hn⟩ := hL
    obtain ⟨⟨u', hu'⟩, hn'⟩ := hL'
    obtain ⟨y, hy, hyc⟩ := K0_comm_mem_of_ne hu hn hu' hn' hLL' (a : X) ha (b : X) hb
    have hyab : y = ⁅a, b⁆ := K.subtype_injective hyc
    rw [← hyab]
    exact hy
  intro w hw
  obtain ⟨hwK, -, -, hwc⟩ := hw
  have hwY : ∀ g : ↥K, ⁅g, (⟨w, hwK⟩ : ↥K)⁆ ∈ pPrimeCore 2 ↥K := by
    intro g
    obtain ⟨y, hy, hyc⟩ := hwc g g.2
    have hyg : y = ⁅g, (⟨w, hwK⟩ : ↥K)⁆ := K.subtype_injective hyc
    rw [← hyg]
    exact hy
  have key := zStar_le_sup_of_sup_eq_top S hSup hcomm hwY
  have hle : pPrimeCore 2 ↥K ⊔ S.sup (fun A => zStar A) ≤
      (pPrimeCoreOf 2 K ⊔ ⨆ (L : Subgroup X) (_ : (∃ u, IsIntrinsicIn X H L u) ∧
          IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n), zStar L).comap K.subtype := by
    refine sup_le ?_ (Finset.sup_le fun A hA => ?_)
    · intro y hy
      exact le_sup_left (a := pPrimeCoreOf 2 K) ⟨y, hy, rfl⟩
    · obtain ⟨L, hL, rfl⟩ := (hmemS A).1 hA
      intro x hx
      have h1 : (x : X) ∈ zStar L :=
        aux_zStar_K0_le_sup_zStar_map (hLK L hL) (Subgroup.mem_map_of_mem K.subtype hx)
      exact le_sup_right (a := pPrimeCoreOf 2 K)
        (le_iSup₂ (f := fun (L : Subgroup X) (_ : (∃ u, IsIntrinsicIn X H L u) ∧
          IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) => zStar L) L hL h1)
  exact hle key

theorem zStar_K0_le_sup_witnesses (n : ℕ) (H : Subgroup X) (W : Set X)
    (hW : ∀ L : Subgroup X, (∃ u, IsIntrinsicIn X H L u) →
      IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n → ∃ u ∈ W, IsIntrinsicIn X H L u) :
    zStar (K0 X n H) ≤ pPrimeCoreOf 2 (K0 X n H) ⊔
      Subgroup.closure {u : X | u ∈ W ∧ ∃ L : Subgroup X, IsIntrinsicIn X H L u ∧
        IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n} := by
  refine (zStar_K0_le_sup n H).trans (sup_le le_sup_left ?_)
  refine iSup₂_le fun L hL => ?_
  obtain ⟨u, huW, hu⟩ := hW L hL.1 hL.2
  have hcomp := hu.isPCompIn_K0 hL.2
  have hO : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 (K0 X n H) :=
    pPrimeCoreOf_le_oddCoreOf hcomp.1 (isPComponent_two_iff.1 hcomp.2).1
  refine (hu.zStar_le_sup_zpowers hL.2).trans (sup_le (hO.trans le_sup_left) ?_)
  exact le_sup_of_le_right (Subgroup.zpowers_le.2 (Subgroup.subset_closure ⟨huW, L, hu, hL.2⟩))

end CFSG.OddStandard.Solomon75
