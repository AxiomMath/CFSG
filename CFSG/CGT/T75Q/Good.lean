module

public import CFSG.CGT.T75Q.Std82
public import CFSG.CGT.T75Q.OrdersK
public import CFSG.CGT.T75Q.KerZ

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem inf_center_le_pCore {R : Type} [Group R] {A : Subgroup R} (hA : IsPGroup 2 A) :
    A ⊓ Subgroup.center R ≤ CFSG.pCore 2 R := by
  have hN : (A ⊓ Subgroup.center R).Normal := ⟨fun n hn g => by
    have h1 := Subgroup.mem_center_iff.1 hn.2 g
    have : g * n * g⁻¹ = n := by rw [h1]; group
    rw [this]
    exact hn⟩
  exact le_sSup ⟨hN, hA.to_inf_left⟩

theorem isPGroup_subgroupOf {T : Subgroup G} (hWC : IsWC T) (V : Subgroup G) :
    IsPGroup 2 (T.subgroupOf V) := by
  have hT2 : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hWC.1
  intro x
  obtain ⟨n, hn⟩ := hT2 ⟨(x : G), Subgroup.mem_subgroupOf.1 x.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥T => (z : G)) hn
  simpa using this

theorem Std82.normalClosure_top_of_gen (s : Std82 T T₁) {V : Subgroup G} (hUV : ugen T ≤ V)
    (hgen : V ≤ Subgroup.closure (classD T ∩ (V : Set G))) :
    Subgroup.normalClosure ((T.subgroupOf V : Subgroup ↥V) : Set ↥V) = ⊤ := by
  classical
  have hfin : Finite G := s.finite
  rw [eq_top_iff]
  intro y _
  have key : ∀ g ∈ Subgroup.closure (classD T ∩ (V : Set G)),
      ∃ hg : g ∈ V, (⟨g, hg⟩ : ↥V) ∈
        Subgroup.normalClosure ((T.subgroupOf V : Subgroup ↥V) : Set ↥V) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem d hd =>
      obtain ⟨y', hy', t, ht, ht1, rfl⟩ := classD_inter_le_deltaOf s.wc s.hN s.h66' s.hTU
        s.exists_ne_one hUV hd.1 hd.2
      have hty : t ∈ V := hUV (s.hTU ht)
      refine ⟨V.mul_mem (V.mul_mem hy' hty) (V.inv_mem hy'), ?_⟩
      have htN : (⟨t, hty⟩ : ↥V) ∈
          Subgroup.normalClosure ((T.subgroupOf V : Subgroup ↥V) : Set ↥V) :=
        Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.2 ht)
      have hmem := Subgroup.normalClosure_normal.conj_mem _ htN ⟨y', hy'⟩
      have e : (⟨y' * t * y'⁻¹, V.mul_mem (V.mul_mem hy' hty) (V.inv_mem hy')⟩ : ↥V) =
          ⟨y', hy'⟩ * ⟨t, hty⟩ * ⟨y', hy'⟩⁻¹ := Subtype.ext rfl
      rw [e]
      exact hmem
    | one => exact ⟨V.one_mem, Subgroup.one_mem _⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨hay, ha'⟩ := iha
      obtain ⟨hby, hb'⟩ := ihb
      exact ⟨V.mul_mem hay hby, Subgroup.mul_mem _ ha' hb'⟩
    | inv a ha iha =>
      obtain ⟨hay, ha'⟩ := iha
      exact ⟨V.inv_mem hay, Subgroup.inv_mem _ ha'⟩
  obtain ⟨hy, hyN⟩ := key (y : G) (hgen y.2)
  exact hyN

theorem Std82.T_inf_pCore (s : Std82 T T₁) {V : Subgroup G} (hHV : hSub T (normIn T₁ T) ≤ V)
    (hcl : Subgroup.normalClosure ((T.subgroupOf V : Subgroup ↥V) : Set ↥V) = ⊤) :
    T.subgroupOf V ⊓ CFSG.pCore 2 ↥V = ⊥ := by
  classical
  have hfin : Finite G := s.finite
  by_contra hne
  obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hqG : (q : G) ≠ 1 := fun h => hq1' (Subtype.ext h)
  have hTyO : T.subgroupOf V ≤ CFSG.pCore 2 ↥V := by
    intro t ht
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact Subgroup.one_mem _
    · obtain ⟨h, hh, hqh⟩ := s.htrans (q : G) (Subgroup.mem_subgroupOf.1 hq.1) hqG (t : G) htT
        (fun h => ht1 (Subtype.ext h))
      have hO := (CFSG.pCore_normal (p := 2) (G := ↥V)).conj_mem q hq.2 ⟨h, hHV hh⟩
      have : (⟨h, hHV hh⟩ * q * ⟨h, hHV hh⟩⁻¹ : ↥V) = t := Subtype.ext (by simpa using hqh)
      rwa [this] at hO
  have hOtop : CFSG.pCore 2 ↥V = ⊤ := by
    rw [eq_top_iff, ← hcl]
    exact Subgroup.normalClosure_le_normal hTyO
  apply s.hH2
  intro h
  have hyO : (⟨(h : G), hHV h.2⟩ : ↥V) ∈ CFSG.pCore 2 ↥V := by
    rw [hOtop]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥V) ⟨_, hyO⟩
  refine ⟨n, Subtype.ext ?_⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥V) => ((z : ↥V) : G)) hn
  simpa using this

section Certified



theorem Std82.good_data
    (s : Std82 T T₁) (h215 : Lemma215Stmt) (hL : ListWCIdentification) {V : Subgroup G}
    (hUV : ugen T ≤ V) (hV : V ≠ ⊤)
    (hcl : Subgroup.normalClosure ((T.subgroupOf V : Subgroup ↥V) : Set ↥V) = ⊤) :
    (jMap ↥V).ker = Subgroup.center ↥V ∧
      Nat.card ↥V = Nat.card (Subgroup.center ↥V) * Nat.card (jQuot ↥V) ∧
      (Nat.card (jQuot ↥V) = 9999360 ∨ Nat.card (jQuot ↥V) = 244823040) := by
  classical
  have hfin : Finite G := s.finite
  have hHV : hSub T (normIn T₁ T) ≤ V := s.hHU.trans hUV
  have hTV : T ≤ V := s.hTH.trans hHV
  have hTO := s.T_inf_pCore hHV hcl
  have hWCV : IsWC (T.subgroupOf V) := isWC_subgroupOf s.wc V hTV
  have hker := ker_jMap_eq_center hWCV hcl hTO
  have hcard : Nat.card ↥V = Nat.card (Subgroup.center ↥V) * Nat.card (jQuot ↥V) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (jMap ↥V).ker
    have h2 : Nat.card (↥V ⧸ (jMap ↥V).ker) = Nat.card (jQuot ↥V) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ jMap_surjective).toEquiv
    rw [h2, hker] at h1
    rw [h1, mul_comm]
  refine ⟨hker, hcard, ?_⟩
  have hlt : Nat.card (↥V ⧸ CFSG.pCore 2 ↥V) < Nat.card G := by
    have h1 : Nat.card (↥V ⧸ CFSG.pCore 2 ↥V) ≤ Nat.card V :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card V < Nat.card G := by
      have hidx := Subgroup.card_mul_index V
      have : V.index ≠ 1 := fun h => hV (Subgroup.index_eq_one.1 h)
      have hpos : 0 < V.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hV0 : 0 < Nat.card V := Nat.card_pos
      have h2' : 2 ≤ V.index := by omega
      have h3 : Nat.card V * 2 ≤ Nat.card G := by
        rw [← hidx]
        exact Nat.mul_le_mul_left _ h2'
      omega
    omega
  obtain ⟨-, -, hstd, hcardT, hnb⟩ := ident_gen s.hc.hy.ind h215 hL s.wc s.hTH hHV s.hHN s.hHC
    s.hHgen s.hH2 hcl hTO (by rw [s.card_T]; norm_num) hlt
  have hker' : T.subgroupOf V ⊓ (jMap ↥V).ker = T.subgroupOf V ⊓ CFSG.pCore 2 ↥V := by
    apply le_antisymm
    · rintro x ⟨hxT, hxk⟩
      refine ⟨hxT, ?_⟩
      have hxc : x ∈ T.subgroupOf V ⊓ Subgroup.center ↥V := ⟨hxT, hker ▸ hxk⟩
      exact inf_center_le_pCore (isPGroup_subgroupOf s.wc V) hxc
    · exact inf_le_inf_left _ pCore_le_ker_jMap
  have hinj : (hSub T (normIn T₁ T)).subgroupOf V ⊓ (jMap ↥V).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwH, hwk⟩
    rw [Subgroup.mem_bot]
    exact jMap_injOn_of_natural hTV s.hHN s.hHC hTO hker' (Subgroup.mem_subgroupOf.1 hwH) hwk
  have hmapcard : Nat.card (((hSub T (normIn T₁ T)).subgroupOf V).map (jMap ↥V)) = 322560 := by
    rw [card_map_of_inf_ker_eq_bot _ _ hinj,
      ← card_hSub_of_natural_four s.hTH s.card_T s.hnat]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHV).toEquiv
  have hdvd : 322560 ∣ Nat.card (jQuot ↥V) :=
    hmapcard ▸ Subgroup.card_subgroup_dvd_card _
  exact card_eq_of_sixteen hstd hnb (by rw [hcardT]; exact s.card_T) hdvd

theorem Std82.jMap_surj
    (s : Std82 T T₁) (h215 : Lemma215Stmt) (hL : ListWCIdentification) {Y : Subgroup G}
    (hUY : ugen T ≤ Y) (hU : ugen T ≠ ⊤) (hY : Y ≠ ⊤)
    (hclU : Subgroup.normalClosure ((T.subgroupOf (ugen T) : Subgroup ↥(ugen T)) :
      Set ↥(ugen T)) = ⊤)
    (hclY : Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊤) :
    (jMap ↥Y).ker = Subgroup.center ↥Y ∧
      ∀ y : ↥Y, ∃ u : ↥(ugen T), jMap ↥Y y = jMap ↥Y (Subgroup.inclusion hUY u) := by
  classical
  have hfin : Finite G := s.finite
  obtain ⟨hkerU, hcardU, hKU⟩ := s.good_data h215 hL (le_refl _) hU hclU
  obtain ⟨hkerY, hcardY, hKY⟩ := s.good_data h215 hL hUY hY hclY
  refine ⟨hkerY, ?_⟩
  let f : ↥(ugen T) →* jQuot ↥Y := (jMap ↥Y).comp (Subgroup.inclusion hUY)
  have hfker : f.ker ≤ Subgroup.center ↥(ugen T) := by
    intro u hu
    have hu' : Subgroup.inclusion hUY u ∈ (jMap ↥Y).ker := hu
    rw [hkerY] at hu'
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := congrArg (fun z : ↥Y => (z : G))
      (Subgroup.mem_center_iff.1 hu' (Subgroup.inclusion hUY g))
    exact Subtype.ext (by simpa using h3)
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hfker
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥(ugen T) ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [h2] at h1
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  have hrange : Nat.card f.range = j * Nat.card (jQuot ↥(ugen T)) := by
    have : Nat.card f.range * Nat.card f.ker =
        (j * Nat.card (jQuot ↥(ugen T))) * Nat.card f.ker := by
      rw [← h1, hcardU, hj]
      ring
    exact Nat.eq_of_mul_eq_mul_right hkpos this
  have hKUdvd : Nat.card (jQuot ↥(ugen T)) ∣ Nat.card f.range := ⟨j, by rw [hrange]; ring⟩
  have hrdvd : Nat.card f.range ∣ Nat.card (jQuot ↥Y) := Subgroup.card_subgroup_dvd_card f.range
  have hKK : Nat.card (jQuot ↥(ugen T)) ∣ Nat.card (jQuot ↥Y) := hKUdvd.trans hrdvd
  have heq : Nat.card (jQuot ↥(ugen T)) = Nat.card (jQuot ↥Y) := by
    rcases hKU with h | h <;> rcases hKY with h' | h'
    · rw [h, h']
    · rw [h, h'] at hKK
      exact absurd hKK (by norm_num)
    · rw [h, h'] at hKK
      exact absurd hKK (by norm_num)
    · rw [h, h']
  have hrange_eq : Nat.card f.range = Nat.card (jQuot ↥Y) :=
    Nat.dvd_antisymm hrdvd (heq ▸ hKUdvd)
  have hrtop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ hrange_eq
  intro y
  have hy : jMap ↥Y y ∈ f.range := by
    rw [hrtop]
    exact Subgroup.mem_top _
  obtain ⟨u, hu⟩ := hy
  exact ⟨u, hu.symm⟩

end Certified

theorem conj_mul_comm {a z t : G} (h : z * t = t * z) : a * z * t * (a * z)⁻¹ = a * t * a⁻¹ := by
  calc a * z * t * (a * z)⁻¹ = a * (z * t * z⁻¹) * a⁻¹ := by group
    _ = a * t * a⁻¹ := by rw [h]; group

theorem Std82.mem_ugen_of_surj (s : Std82 T T₁) {Y : Subgroup G} (hUY : ugen T ≤ Y)
    (hker : (jMap ↥Y).ker = Subgroup.center ↥Y)
    (hsurj : ∀ y : ↥Y, ∃ u : ↥(ugen T), jMap ↥Y y = jMap ↥Y (Subgroup.inclusion hUY u)) {d : G}
    (hd : d ∈ classD T) (hdY : d ∈ Y) : d ∈ ugen T := by
  have hfin : Finite G := s.finite
  obtain ⟨y, hy, t, ht, ht1, rfl⟩ := classD_inter_le_deltaOf s.wc s.hN s.h66' s.hTU
    s.exists_ne_one hUY hd hdY
  obtain ⟨u, hu⟩ := hsurj ⟨y, hy⟩
  obtain ⟨z, hzdef⟩ : ∃ z : ↥Y, z = (Subgroup.inclusion hUY u)⁻¹ * ⟨y, hy⟩ := ⟨_, rfl⟩
  have hz : z ∈ (jMap ↥Y).ker := by
    rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, ← hu, inv_mul_cancel]
  rw [hker] at hz
  have hzt := Subgroup.mem_center_iff.1 hz ⟨t, hUY (s.hTU ht)⟩
  have hyz : y = (u : G) * (z : G) := by
    have : (⟨y, hy⟩ : ↥Y) = Subgroup.inclusion hUY u * z := by rw [hzdef]; group
    exact congrArg Subtype.val this
  have hcomm : (z : G) * t = t * (z : G) := (congrArg (fun w : ↥Y => (w : G)) hzt).symm
  have key : y * t * y⁻¹ = (u : G) * t * (u : G)⁻¹ := by
    rw [hyz]
    exact conj_mul_comm hcomm
  rw [key]
  exact (ugen T).mul_mem ((ugen T).mul_mem u.2 (s.hTU ht)) ((ugen T).inv_mem u.2)

end CFSG.CGT.T75Q
