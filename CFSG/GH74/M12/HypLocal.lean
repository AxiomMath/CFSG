module

public import CFSG.GH74.M12.HypModel
public import CFSG.GH74.M12.HypAsc

public section

namespace CFSG.GH74.M12.Hyp

open Subgroup CFSG CFSG.GH74

@[expose] def tblSubgroup (L : List (List Nat)) (hone : tid ∈ L)
    (hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L) (hinv : ∀ s ∈ L, tinv s ∈ L) : Subgroup ↥CJ where
  carrier := {x | tauC x ∈ L}
  mul_mem' := by
    intro a b ha hb
    show tauC (a * b) ∈ L
    rw [tauC_mul]
    exact hmul _ ha _ hb
  one_mem' := by
    show tauC 1 ∈ L
    rw [tauC_one]
    exact hone
  inv_mem' := by
    intro a ha
    show tauC a⁻¹ ∈ L
    rw [tauC_inv]
    exact hinv _ ha

theorem tauC_pow (x : ↥CJ) (n : Nat) : tauC (x ^ n) = tpow (tauC x) n := by
  induction n with
  | zero => rw [pow_zero, tauC_one]; rfl
  | succ n ih => rw [pow_succ', tauC_mul, ih]; rfl

theorem card_of_tauC
    {P : ↥CJ → Prop} (L : List (List Nat)) (hL : L.Nodup)
    (hsub : ∀ t ∈ L, t ∈ HT) (hP : ∀ x, P x ↔ tauC x ∈ L) :
    Nat.card {x // P x} = L.length := by
  have e : {x // P x} ≃ {t // t ∈ L} :=
    Equiv.ofBijective (fun x => ⟨tauC x.1, (hP x.1).1 x.2⟩)
      ⟨fun a b hab => Subtype.ext (tauC_injective (congrArg Subtype.val hab)), by
        rintro ⟨t, ht⟩
        obtain ⟨x, hx⟩ := tauC_real t (hsub t ht)
        refine ⟨⟨x, (hP x).2 (by rw [hx]; exact ht)⟩, Subtype.ext hx⟩⟩
  rw [Nat.card_congr e, card_mem_list L hL]

theorem card_CJ :
    Nat.card ↥CJ = 192 := by
  have := card_of_tauC (P := fun _ => True) HT HT_nodup (fun _ h => h)
    (fun x => by simp [tauC_mem x])
  rw [HT_length] at this
  rw [← this]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem card_tblSubgroup {L : List (List Nat)} {hone : tid ∈ L}
    {hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L} {hinv : ∀ s ∈ L, tinv s ∈ L} (hL : L.Nodup)
    (hsub : ∀ t ∈ L, t ∈ HT) : Nat.card ↥(tblSubgroup L hone hmul hinv) = L.length :=
  card_of_tauC (P := fun x => x ∈ tblSubgroup L hone hmul hinv) L hL hsub (fun _ => Iff.rfl)

theorem normal_tblSubgroup
    {L : List (List Nat)} {hone : tid ∈ L}
    {hmul : ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L} {hinv : ∀ s ∈ L, tinv s ∈ L}
    (hn : ∀ c ∈ HT, ∀ q ∈ L, tmul (tmul c q) (tinv c) ∈ L) :
    (tblSubgroup L hone hmul hinv).Normal where
  conj_mem n hn' g := by
    show tauC (g * n * g⁻¹) ∈ L
    rw [tauC_mul, tauC_mul, tauC_inv]
    exact hn _ (tauC_mem g) _ hn'

@[expose] def Qsub :
    Subgroup ↥CJ := tblSubgroup QT tid_mem_QT QT_mul QT_inv

@[expose] def Q1sub :
    Subgroup ↥CJ := tblSubgroup Q1T tid_mem_Q1T Q1T_mul Q1T_inv

@[expose] def Q2sub :
    Subgroup ↥CJ := tblSubgroup Q2T tid_mem_Q2T Q2T_mul Q2T_inv

theorem mem_Qsub {x : ↥CJ} : x ∈ Qsub ↔ tauC x ∈ QT := Iff.rfl

theorem mem_Q1sub {x : ↥CJ} : x ∈ Q1sub ↔ tauC x ∈ Q1T := Iff.rfl

theorem mem_Q2sub {x : ↥CJ} : x ∈ Q2sub ↔ tauC x ∈ Q2T := Iff.rfl

theorem QT_sub_HT : ∀ t ∈ QT, t ∈ HT := fun _ ht => (mem_QT_iff.1 ht).1

theorem card_Qsub : Nat.card ↥Qsub = 32 := by
  rw [Qsub, card_tblSubgroup QT_nodup QT_sub_HT, QT_length]

theorem card_Q1sub : Nat.card ↥Q1sub = 8 := by
  rw [Q1sub, card_tblSubgroup Q1T_nodup (fun t ht => QT_sub_HT t (Q1T_sub t ht)), Q1T_length]

theorem card_Q2sub : Nat.card ↥Q2sub = 8 := by
  rw [Q2sub, card_tblSubgroup Q2T_nodup (fun t ht => QT_sub_HT t (Q2T_sub t ht)), Q2T_length]

theorem Qsub_normal
    : Qsub.Normal := normal_tblSubgroup QT_normal

instance instNormalQsub :
    Qsub.Normal := Qsub_normal

theorem Q1sub_normal
    : Q1sub.Normal := normal_tblSubgroup Q1T_normal

theorem Q2sub_normal
    : Q2sub.Normal := normal_tblSubgroup Q2T_normal

theorem isPGroup_Qsub : IsPGroup 2 ↥Qsub :=
  IsPGroup.of_card (n := 5) (by rw [card_Qsub]; norm_num)

@[expose] def zJ : ↥CJ := ⟨Jelt, Jelt_mem_CJ⟩

theorem tauC_zJ : tauC zJ = JT := tbl_bfJ

theorem quotient_perm_three
    : Nonempty (↥CJ ⧸ Qsub ≃* Equiv.Perm (Fin 3)) := by
  have hcard : Nat.card (↥CJ ⧸ Qsub) = 6 := by
    have h := Subgroup.card_mul_index Qsub
    rw [card_Qsub, card_CJ] at h
    rw [← Subgroup.index_eq_card]
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := HQ_noncomm
  obtain ⟨cx, rfl⟩ := tauC_real c hc
  obtain ⟨dx, rfl⟩ := tauC_real d hd
  refine nonempty_mulEquiv_perm_three_of_card_six hcard (QuotientGroup.mk cx)
    (QuotientGroup.mk dx) ?_
  intro h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  apply hcd
  have h2 : tauC ((cx * dx)⁻¹ * (dx * cx)) ∈ QT := h
  rwa [tauC_mul, tauC_inv, tauC_mul, tauC_mul] at h2

theorem pCore_CJ :
    pCore 2 ↥CJ = Qsub := by
  apply le_antisymm
  · obtain ⟨e3⟩ := quotient_perm_three
    intro k hk
    have hK2 : IsPGroup 2 (pCore 2 ↥CJ) := pCore_isPGroup
    have h1 : ((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).Normal :=
      Subgroup.Normal.map (pCore_normal (G := ↥CJ) (p := 2)) (QuotientGroup.mk' Qsub)
        (QuotientGroup.mk'_surjective Qsub)
    have hN : (((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom).Normal :=
      Subgroup.Normal.map h1 e3.toMonoidHom e3.surjective
    have hNp : IsPGroup 2 (((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom) :=
      (hK2.map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom
    have hbot := eq_bot_of_normal_isPGroup_perm_three
      (((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom) hNp
    have hmem : e3 (QuotientGroup.mk' Qsub k) ∈
        ((pCore 2 ↥CJ).map (QuotientGroup.mk' Qsub)).map e3.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hk)
    rw [hbot] at hmem
    have h2 : e3 (QuotientGroup.mk' Qsub k) = 1 := by simpa using hmem
    have h3 : QuotientGroup.mk' Qsub k = 1 := e3.map_eq_one_iff.1 h2
    exact (QuotientGroup.eq_one_iff k).1 h3
  · exact le_sSup ⟨Qsub_normal, isPGroup_Qsub⟩

@[expose] def tauQ (x : ↥Qsub) : List Nat := tauC x.1

theorem tauQ_injective : Function.Injective tauQ := fun _ _ h =>
  Subtype.ext (tauC_injective h)

theorem tauQ_mem (x : ↥Qsub) : tauQ x ∈ QT := x.2

theorem tauQ_mul
    (x y : ↥Qsub) : tauQ (x * y) = tmul (tauQ x) (tauQ y) := tauC_mul x.1 y.1

theorem tauQ_inv
    (x : ↥Qsub) : tauQ x⁻¹ = tinv (tauQ x) := tauC_inv x.1

theorem tauQ_real : ∀ t ∈ QT, ∃ x : ↥Qsub, tauQ x = t := by
  intro t ht
  obtain ⟨x, hx⟩ := tauC_real t (QT_sub_HT t ht)
  exact ⟨⟨x, by rw [mem_Qsub, hx]; exact ht⟩, hx⟩

theorem tid_ne_JT : tid ≠ JT := by decide +kernel

theorem mem_center_Qsub
    {x : ↥Qsub} : x ∈ center ↥Qsub ↔ tauQ x = tid ∨ tauQ x = JT := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    refine (QT_center _ (tauQ_mem x)).1 ?_
    intro t ht
    obtain ⟨y, rfl⟩ := tauQ_real t ht
    rw [← tauQ_mul, ← tauQ_mul, h y]
  · intro h y
    apply tauQ_injective
    rw [tauQ_mul, tauQ_mul]
    exact ((QT_center _ (tauQ_mem x)).2 h _ (tauQ_mem y)).symm

theorem card_center_Qsub : Nat.card ↥(center ↥Qsub) = 2 := by
  have e : ↥(center ↥Qsub) ≃ {t // t ∈ [tid, JT]} :=
    Equiv.ofBijective (fun c => ⟨tauQ c.1, by
        have := mem_center_Qsub.1 c.2
        simpa using this⟩)
      ⟨fun a b hab => Subtype.ext (tauQ_injective (congrArg Subtype.val hab)), by
        rintro ⟨t, ht⟩
        have ht' : t = tid ∨ t = JT := by simpa using ht
        rcases ht' with rfl | rfl
        · exact ⟨⟨1, Subgroup.one_mem _⟩, Subtype.ext (tauC_one)⟩
        · obtain ⟨y, hy⟩ := tauQ_real JT JT_mem_QT
          exact ⟨⟨y, mem_center_Qsub.2 (Or.inr hy)⟩, Subtype.ext hy⟩⟩
  rw [Nat.card_congr e, card_mem_list [tid, JT] (by simp [tid_ne_JT])]
  rfl

theorem isElementaryAbelian_Qsub :
    IsElementaryAbelian 2 (↥Qsub ⧸ center ↥Qsub) := by
  have hcomm : ∀ a b : ↥Qsub ⧸ center ↥Qsub, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_center_Qsub]
    rw [tauQ_mul, tauQ_inv, tauQ_mul, tauQ_mul]
    exact QT_comm _ (tauQ_mem x) _ (tauQ_mem y)
  have hexp : Monoid.exponent (↥Qsub ⧸ center ↥Qsub) ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    induction a using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_Qsub, pow_two, tauQ_mul]
    exact QT_sq _ (tauQ_mem x)
  exact { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := hexp }

theorem nontrivial_quotient_Qsub :
    Nontrivial (↥Qsub ⧸ center ↥Qsub) := by
  obtain ⟨s, hs, hs1, hs2⟩ := QT_noncentral
  obtain ⟨x, rfl⟩ := tauQ_real s hs
  refine ⟨⟨QuotientGroup.mk x, 1, ?_⟩⟩
  intro h
  rw [QuotientGroup.eq_one_iff, mem_center_Qsub] at h
  rcases h with h | h
  · exact hs1 h
  · exact hs2 h

theorem isExtraspecial_Qsub : IsExtraspecial 2 ↥Qsub where
  center_order_p := card_center_Qsub
  quotient_elementary_abelian := isElementaryAbelian_Qsub
  quotient_nontrivial := nontrivial_quotient_Qsub

theorem localHyp_CJ :
    LocalHyp ↥CJ zJ where
  card_eq := card_CJ
  card_core := by rw [pCore_CJ]; exact card_Qsub
  extraspecial := by rw [pCore_CJ]; exact isExtraspecial_Qsub
  quotient_S3 := by
    obtain ⟨e3⟩ := quotient_perm_three
    exact ⟨(QuotientGroup.quotientMulEquivOfEq pCore_CJ).trans e3⟩
  centralizer_X := by
    intro x hx q hq hcomm
    rw [pCore_CJ] at hq
    have hx3 : x * (x * x) = 1 := by
      have h3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      rw [← pow_three]; exact h3
    have hx1 : x ≠ 1 := by
      intro h; rw [h, orderOf_one] at hx; omega
    have h1 : tmul (tauC x) (tmul (tauC x) (tauC x)) = tid := by
      rw [← tauC_mul, ← tauC_mul, hx3, tauC_one]
    have h2 : tauC x ≠ tid := by
      intro h
      apply hx1
      apply tauC_injective
      rw [h, tauC_one]
    have h3 : tmul (tauC q) (tauC x) = tmul (tauC x) (tauC q) := by
      rw [← tauC_mul, ← tauC_mul, hcomm.symm]
    rcases QT_order3 (tauC x) (tauC_mem x) h1 h2 (tauC q) hq h3 with h | h
    · have : q = 1 := tauC_injective (by rw [h, tauC_one])
      rw [this]; exact Subgroup.one_mem _
    · have : q = zJ := tauC_injective (by rw [h, tauC_zJ])
      rw [this]; exact Subgroup.mem_zpowers _

@[expose] def q8T (x y : List Nat) : QuaternionGroup 2 → List Nat
  | .a i => tpow x i.val
  | .xa i => tmul (tpow x ((4 - i.val) % 4)) y

theorem q8T_one : q8T x1T y1T 1 = tid := by decide +kernel

theorem q8T_mul : ∀ g h : QuaternionGroup 2,
    tmul (q8T x1T y1T g) (q8T x1T y1T h) = q8T x1T y1T (g * h) := by decide +kernel

theorem q8T_injective : ∀ g h : QuaternionGroup 2,
    q8T x1T y1T g = q8T x1T y1T h → g = h := by decide +kernel

theorem q8T_mem : ∀ g : QuaternionGroup 2, q8T x1T y1T g ∈ Q1T := by decide +kernel

theorem q8T_surj : ∀ t ∈ Q1T, ∃ g : QuaternionGroup 2, q8T x1T y1T g = t := by decide +kernel

theorem q8_a1_pow4 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 := by decide +kernel

theorem q8_a1_sq_ne : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide +kernel

theorem q8_xa0_sq : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
    (QuaternionGroup.a 1) ^ 2 := by decide +kernel

theorem q8_xa0_a1 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 =
    (QuaternionGroup.a 1) ^ 3 * QuaternionGroup.xa 0 := by decide +kernel

theorem q8_gen : ∀ g : QuaternionGroup 2, ∃ i < 4, ∃ j < 2,
    g = (QuaternionGroup.a 1) ^ i * (QuaternionGroup.xa 0) ^ j := by decide +kernel

theorem card_q8 : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem eq_of_q8_gens {K L : Subgroup ↥CJ} (iso : ↥K ≃* QuaternionGroup 2)
    (hL : Nat.card ↥L = 8)
    (hx : ((iso.symm (QuaternionGroup.a 1) : ↥K) : ↥CJ) ∈ L)
    (hy : ((iso.symm (QuaternionGroup.xa 0) : ↥K) : ↥CJ) ∈ L) : K = L := by
  have hle : K ≤ L := by
    intro k hk
    obtain ⟨i, -, j, -, hg⟩ := q8_gen (iso ⟨k, hk⟩)
    have h1 : (⟨k, hk⟩ : ↥K) =
        iso.symm ((QuaternionGroup.a 1) ^ i * (QuaternionGroup.xa 0) ^ j) := by
      rw [← hg]; simp
    have hk' : k = ((iso.symm (QuaternionGroup.a 1) : ↥K) : ↥CJ) ^ i *
        ((iso.symm (QuaternionGroup.xa 0) : ↥K) : ↥CJ) ^ j := by
      have := congrArg Subtype.val h1
      rw [map_mul, map_pow, map_pow] at this
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using this
    rw [hk']
    exact mul_mem (pow_mem hx i) (pow_mem hy j)
  have hK : Nat.card ↥K = 8 := by rw [Nat.card_congr iso.toEquiv, card_q8]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hL, hK])

theorem q8_normal_CJ
    : ∀ K ∈ q8Subgroups (pCore 2 ↥CJ), K.Normal := by
  rintro K ⟨hle, ⟨iso⟩⟩
  rw [pCore_CJ] at hle
  obtain ⟨φ, hφ⟩ : ∃ φ : QuaternionGroup 2 →* ↥CJ, ∀ g, φ g = ((iso.symm g : ↥K) : ↥CJ) :=
    ⟨K.subtype.comp iso.symm.toMonoidHom, fun g => rfl⟩
  have hφinj : Function.Injective φ := by
    intro a b h
    apply iso.symm.injective
    apply Subtype.ext
    rw [← hφ, ← hφ]
    exact h
  have hφQ : ∀ g, tauC (φ g) ∈ QT := by
    intro g
    have h1 : ((iso.symm g : ↥K) : ↥CJ) ∈ K := (iso.symm g).2
    rw [hφ]
    exact (mem_Qsub).1 (hle h1)
  have hx4 : φ (QuaternionGroup.a 1) ^ 4 = 1 := by rw [← map_pow, q8_a1_pow4, map_one]
  have hx2 : φ (QuaternionGroup.a 1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro h
    exact q8_a1_sq_ne (hφinj (by rw [h, map_one]))
  have hyy : φ (QuaternionGroup.xa 0) * φ (QuaternionGroup.xa 0) = φ (QuaternionGroup.a 1) ^ 2 := by
    rw [← map_mul, q8_xa0_sq, map_pow]
  have hyx : φ (QuaternionGroup.xa 0) * φ (QuaternionGroup.a 1) =
      φ (QuaternionGroup.a 1) ^ 3 * φ (QuaternionGroup.xa 0) := by
    rw [← map_mul, q8_xa0_a1, map_mul, map_pow]
  have h4 : tpow (tauC (φ (QuaternionGroup.a 1))) 4 = tid := by
    rw [← tauC_pow, hx4, tauC_one]
  have h2 : tpow (tauC (φ (QuaternionGroup.a 1))) 2 ≠ tid := by
    intro h
    apply hx2
    apply tauC_injective
    rw [tauC_pow, h, tauC_one]
  have hyy' : tmul (tauC (φ (QuaternionGroup.xa 0))) (tauC (φ (QuaternionGroup.xa 0))) =
      tpow (tauC (φ (QuaternionGroup.a 1))) 2 := by
    rw [← tauC_mul, hyy, tauC_pow]
  have hyx' : tmul (tauC (φ (QuaternionGroup.xa 0))) (tauC (φ (QuaternionGroup.a 1))) =
      tmul (tpow (tauC (φ (QuaternionGroup.a 1))) 3) (tauC (φ (QuaternionGroup.xa 0))) := by
    rw [← tauC_mul, hyx, tauC_mul, tauC_pow]
  rcases Q8_classification _ (hφQ _) _ (hφQ _) h4 h2 hyy' hyx' with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩
  · have hx1' : ((iso.symm (QuaternionGroup.a 1) : ↥K) : ↥CJ) ∈ Q1sub := by
      rw [← hφ]; exact hx1
    have hy1' : ((iso.symm (QuaternionGroup.xa 0) : ↥K) : ↥CJ) ∈ Q1sub := by
      rw [← hφ]; exact hy1
    have : K = Q1sub := eq_of_q8_gens iso card_Q1sub hx1' hy1'
    rw [this]; exact Q1sub_normal
  · have hx1' : ((iso.symm (QuaternionGroup.a 1) : ↥K) : ↥CJ) ∈ Q2sub := by
      rw [← hφ]; exact hx1
    have hy1' : ((iso.symm (QuaternionGroup.xa 0) : ↥K) : ↥CJ) ∈ Q2sub := by
      rw [← hφ]; exact hy1
    have : K = Q2sub := eq_of_q8_gens iso card_Q2sub hx1' hy1'
    rw [this]; exact Q2sub_normal

theorem q8T_mem_HT (g : QuaternionGroup 2) : q8T x1T y1T g ∈ HT :=
  QT_sub_HT _ (Q1T_sub _ (q8T_mem g))

noncomputable def q8Hom : QuaternionGroup 2 →* ↥CJ where
  toFun g := Classical.choose (tauC_real (q8T x1T y1T g) (q8T_mem_HT g))
  map_one' := by
    apply tauC_injective
    rw [Classical.choose_spec (tauC_real (q8T x1T y1T 1) (q8T_mem_HT 1)), q8T_one, tauC_one]
  map_mul' g h := by
    apply tauC_injective
    rw [tauC_mul, Classical.choose_spec (tauC_real (q8T x1T y1T g) (q8T_mem_HT g)),
      Classical.choose_spec (tauC_real (q8T x1T y1T h) (q8T_mem_HT h)),
      Classical.choose_spec (tauC_real (q8T x1T y1T (g * h)) (q8T_mem_HT (g * h))), q8T_mul]

theorem tauC_q8Hom
    (g : QuaternionGroup 2) : tauC (q8Hom g) = q8T x1T y1T g :=
  Classical.choose_spec (tauC_real (q8T x1T y1T g) (q8T_mem_HT g))

theorem q8Hom_injective : Function.Injective q8Hom := by
  intro g h hgh
  apply q8T_injective
  rw [← tauC_q8Hom, ← tauC_q8Hom, hgh]

theorem q8Hom_range : q8Hom.range = Q1sub := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    show tauC (q8Hom g) ∈ Q1T
    rw [tauC_q8Hom]
    exact q8T_mem g
  · intro hx
    obtain ⟨g, hg⟩ := q8T_surj (tauC x) hx
    exact ⟨g, tauC_injective (by rw [tauC_q8Hom, hg])⟩

theorem Q1sub_mulEquiv : Nonempty (↥Q1sub ≃* QuaternionGroup 2) :=
  ⟨(MulEquiv.subgroupCongr q8Hom_range.symm).trans (MonoidHom.ofInjective q8Hom_injective).symm⟩

theorem exists_q8_normal_CJ
    : ∃ K ∈ q8Subgroups (pCore 2 ↥CJ), K.Normal := by
  refine ⟨Q1sub, ⟨?_, Q1sub_mulEquiv⟩, Q1sub_normal⟩
  rw [pCore_CJ]
  intro x hx
  exact (mem_Qsub).2 (Q1T_sub _ hx)

theorem centralizer_Jelt : centralizer ({Jelt} : Set G12) = CJ := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, mem_CJ]
  constructor
  · intro h
    exact (congrArg Subtype.val h).symm
  · intro h
    exact Subtype.ext h.symm

@[expose] def eCJ : ↥(centralizer ({Jelt} : Set G12)) ≃* ↥CJ :=
  MulEquiv.subgroupCongr centralizer_Jelt

theorem eCJ_zElt : eCJ (zElt' Jelt) = zJ := Subtype.ext rfl

theorem localHyp_centralizer_Jelt :
    LocalHyp ↥(centralizer ({Jelt} : Set G12)) (zElt' Jelt) :=
  LocalHyp.of_mulEquiv eCJ.symm ((eCJ.symm_apply_eq).2 eCJ_zElt.symm) localHyp_CJ

theorem exists_xX : ∃ x : ↥CJ, x ∈ Qsub ∧ x.1 = Xelt := by
  have hX : XT ∈ QT := XT_mem_QT
  obtain ⟨x, hx⟩ := tauC_real XT (QT_sub_HT _ hX)
  refine ⟨x, by rw [mem_Qsub, hx]; exact hX, ?_⟩
  apply Subtype.ext
  apply tbl_injective
  show tauC x = tbl bfX
  rw [hx, tbl_bfX]

theorem weakly_closed_Jelt
    : ∃ g : G12, g * Jelt * g⁻¹ ≠ Jelt ∧
    ∃ q ∈ pCore 2 ↥(centralizer ({Jelt} : Set G12)), (q : G12) = g * Jelt * g⁻¹ := by
  obtain ⟨h, hh⟩ := exists_conj_Jelt_Xelt
  obtain ⟨x, hxQ, hxX⟩ := exists_xX
  refine ⟨h, by rw [hh]; exact Xelt_ne_Jelt, eCJ.symm x, ?_, ?_⟩
  · have hx : x ∈ pCore 2 ↥CJ := by rw [pCore_CJ]; exact hxQ
    have := Subgroup.mem_map_of_mem eCJ.symm.toMonoidHom hx
    rwa [pCore_map_iso 2 eCJ.symm] at this
  · rw [hh]
    exact hxX

theorem asc03Hyp_Jelt :
    Asc03Hyp G12 Jelt :=
  asc03Hyp_of_local Jelt orderOf_Jelt localHyp_centralizer_Jelt weakly_closed_Jelt

theorem q8_normal_Jelt :
    ∀ K ∈ q8Subgroups (pCore 2 ↥(centralizer ({Jelt} : Set G12))), K.Normal :=
  q8_normal_of_mulEquiv eCJ.symm q8_normal_CJ

theorem exists_q8_normal_Jelt :
    ∃ K ∈ q8Subgroups (pCore 2 ↥(centralizer ({Jelt} : Set G12))), K.Normal :=
  exists_q8_normal_of_mulEquiv eCJ.symm exists_q8_normal_CJ

theorem asc03_of_central_involution
    (z : G12) (hz : IsCentralInvolution z) :
    Asc03Hyp G12 z ∧
      ∀ K ∈ q8Subgroups (pCore 2 ↥(centralizer ({z} : Set G12))), K.Normal := by
  obtain ⟨g, rfl⟩ := exists_conj_of_central_involution z hz
  have hlocz : LocalHyp ↥(centralizer ({g * Jelt * g⁻¹} : Set G12)) (zElt' (g * Jelt * g⁻¹)) :=
    LocalHyp.of_mulEquiv (conjCentralizerEquiv g Jelt) (conjCentralizerEquiv_zElt g Jelt)
      localHyp_centralizer_Jelt
  refine ⟨asc03Hyp_of_local _ hz.1 hlocz ?_,
    q8_normal_of_mulEquiv (conjCentralizerEquiv g Jelt) q8_normal_Jelt⟩
  obtain ⟨h, hne, q, hq, hqe⟩ := weakly_closed_Jelt
  refine ⟨g * h * g⁻¹, ?_, conjCentralizerEquiv g Jelt q, ?_, ?_⟩
  · intro hcon
    apply hne
    calc h * Jelt * h⁻¹ = g⁻¹ * ((g * h * g⁻¹) * (g * Jelt * g⁻¹) * (g * h * g⁻¹)⁻¹) * g := by
          group
      _ = g⁻¹ * (g * Jelt * g⁻¹) * g := by rw [hcon]
      _ = Jelt := by group
  · have := Subgroup.mem_map_of_mem (conjCentralizerEquiv g Jelt).toMonoidHom hq
    rwa [pCore_map_iso 2 (conjCentralizerEquiv g Jelt)] at this
  · rw [conjCentralizerEquiv_apply, hqe]
    group

end CFSG.GH74.M12.Hyp
