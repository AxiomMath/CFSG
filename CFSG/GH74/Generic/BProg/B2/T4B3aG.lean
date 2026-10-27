module

public import CFSG.GH74.Generic.BProg.B2.T4B3aModels
public import CFSG.GH74.Generic.BProg.B2.T1Comp
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.B3aG

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B2.T4.B3aGen
open scoped commutatorElement

section Inj

variable {J Y : Type} [Group J] [Group Y]

theorem isCompIn_map_of_injective {φ : J →* Y} (hφ : Function.Injective φ) {C L : Subgroup J}
    (h : IsCompIn C L) : IsCompIn (C.map φ) (L.map φ) := by
  obtain ⟨hLC, hcomp⟩ := h
  refine ⟨Subgroup.map_mono hLC, ?_⟩
  let e : ↥C ≃* ↥(C.map φ) := C.equivMapOfInjective φ hφ
  have hmap : (L.subgroupOf C).map e.toMonoidHom = (L.map φ).subgroupOf (C.map φ) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
      exact ⟨⟨k, hLC hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
  have := CFSG.LocalCores.isComponent_map_mulEquiv e hcomp
  rwa [hmap] at this

theorem isCompIn_of_map_injective {φ : J →* Y} (hφ : Function.Injective φ) {C L : Subgroup J}
    (h : IsCompIn (C.map φ) (L.map φ)) : IsCompIn C L := by
  obtain ⟨hLC, hcomp⟩ := h
  have hLC' : L ≤ C := (Subgroup.map_le_map_iff_of_injective hφ).1 hLC
  refine ⟨hLC', ?_⟩
  let e : ↥C ≃* ↥(C.map φ) := C.equivMapOfInjective φ hφ
  have hmap : ((L.map φ).subgroupOf (C.map φ)).map e.symm.toMonoidHom = L.subgroupOf C := by
    ext z
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := hφ hwz
      rw [← this]
      exact hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have := CFSG.LocalCores.isComponent_map_mulEquiv e.symm hcomp
  rwa [hmap] at this

theorem map_subtype_centralizer (H : Subgroup Y) (t : ↥H) :
    (centralizer ({t} : Set ↥H)).map H.subtype = H ⊓ centralizer ({(t : Y)} : Set Y) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, congrArg Subtype.val hw⟩
  · rintro ⟨hzH, hz⟩
    exact ⟨⟨z, hzH⟩, Subtype.ext hz, rfl⟩

theorem exists_two_ne [Finite Y] (H : Subgroup Y) (h3 : 3 ≤ Nat.card ↥H) :
    ∃ a ∈ H, ∃ b ∈ H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hne : H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h3
    omega
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  by_contra hcon
  push Not at hcon
  have hsub : (H : Set Y) ⊆ {1, (a : Y)} := by
    intro b hb
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    · exact Or.inr (hcon a a.2 b hb (fun h => ha1 (Subtype.ext h)) hb1).symm
  have h2 : Nat.card ↥H ≤ 2 := by
    calc Nat.card ↥H = (H : Set Y).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, (a : Y)} : Set Y).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  omega

end Inj

section Group

variable {G : Type} [Group G] [Finite G]

theorem mk_ne_one_of_sq {M : Subgroup G} {g : ↥M} (hg : g * g = 1) (hg1 : g ≠ 1) :
    QuotientGroup.mk' (pPrimeCore 2 ↥M) g ≠ 1 := by
  intro h
  have hodd := T3S1.odd_orderOf_of_mk_eq_one g h
  have h2 : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hg) hg1
  rw [h2] at hodd
  exact absurd hodd (by decide)

theorem exists_invol_lift {M : Subgroup G} {z : Mbar M} (hz : z * z = 1) :
    ∃ g : ↥M, g * g = 1 ∧ QuotientGroup.mk' (pPrimeCore 2 ↥M) g = z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) z
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hg2 : (g ^ m) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hzm : (QuotientGroup.mk' (pPrimeCore 2 ↥M) g) ^ m = QuotientGroup.mk' (pPrimeCore 2 ↥M) g := by
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, hz, one_pow, one_mul]
  refine ⟨g ^ m, ?_, by rw [map_pow, hzm]⟩
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) (g ^ m * g ^ m) = 1 := by
    rw [map_mul, map_pow, hzm, hz]
  have hmem : g ^ m * g ^ m ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h1
  have hpow : (g ^ m * g ^ m) ^ (2 ^ k) = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hg2, one_pow]
  exact eq_one_of_isPGroup_of_mem_pPrimeCore (isPGroup_zpowers_of_pow_two_pow_eq_one hpow)
    (Subgroup.mem_zpowers _) hmem

theorem Q_le_CMbar_of_barK {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1 x K M Q H) (hq : IsQuasisimple ↥(barIn M K)) {a : Mbar M}
    (haK : a ∈ barIn M K) (ha2 : orderOf a = 2) : Q ≤ CMbar M K := by
  have hKM : K ≤ M := h1.K_le
  set N : Subgroup (Mbar M) := barIn M (pPrimeCoreOf 2 K) with hN
  have hNK : N ≤ barIn M K :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M (TwoThin.pPrimeCoreOf_le K))
  have hNn : (N.subgroupOf (barIn M K)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨u, hu, hun⟩ := hn
    obtain ⟨v, hv, hvk⟩ := k.2
    have hu1 : (u : G) ∈ pPrimeCoreOf 2 K := hu
    have hv : (v : G) ∈ K := hv
    obtain ⟨u', hu', hu'e⟩ := hu1
    simp only [Subgroup.coe_subtype] at hu'e
    have hvu : (v : G) * (u : G) * (v : G)⁻¹ ∈ pPrimeCoreOf 2 K := by
      refine ⟨⟨(v : G), hv⟩ * u' * ⟨(v : G), hv⟩⁻¹, ?_, ?_⟩
      · exact (CFSG.pPrimeCore_normal (p := 2) (G := ↥K)).conj_mem _ hu' _
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hu'e]
    refine ⟨v * u * v⁻¹, hvu, ?_⟩
    simp only [map_mul, map_inv, hun, hvk, Subgroup.coe_mul, Subgroup.coe_inv]
  have hNc : ∀ n ∈ N, ∀ k ∈ barIn M K, n * k = k * n := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hNn with htop | hcen
    · exfalso
      have haN : a ∈ N := by
        have : (⟨a, haK⟩ : ↥(barIn M K)) ∈ N.subgroupOf (barIn M K) := by rw [htop]; exact mem_top _
        exact Subgroup.mem_subgroupOf.1 this
      obtain ⟨u, hu, rfl⟩ := haN
      have hu1 : (u : G) ∈ pPrimeCoreOf 2 K := hu
      obtain ⟨u', hu', hu'e⟩ := hu1
      have hodd : Odd (orderOf u') := by
        have hdvd : orderOf u' ∣ Nat.card (pPrimeCore 2 ↥K) := Subgroup.orderOf_dvd_natCard _ hu'
        exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card.coprime_dvd_right hdvd)
      have h1' : orderOf u = orderOf u' := by
        rw [← Subgroup.orderOf_coe u, ← hu'e, Subgroup.coe_subtype, Subgroup.orderOf_coe]
      have hdvd := orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥M)) u
      rw [ha2, h1'] at hdvd
      exact absurd (Odd.of_dvd_nat hodd hdvd) (by decide)
    · intro n hn k hk
      have := Subgroup.mem_center_iff.1 (hcen (Subgroup.mem_subgroupOf.2 hn : (⟨n, hNK hn⟩ :
        ↥(barIn M K)) ∈ N.subgroupOf (barIn M K))) ⟨k, hk⟩
      exact (congrArg Subtype.val this).symm
  have hperf : ⁅barIn M K, barIn M K⁆ = barIn M K := Subgroup.isPerfect_iff.mp hq.1
  intro q hq'
  have hqM : q ∈ M := h1.Q_le hq'
  have hqC : q ∈ CxK x K := hs.sylowQ.le hq'
  have hqS : ∀ k ∈ K, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := (Subgroup.mem_inf.1 hqC).2.2.2
  set qb : Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨q, hqM⟩ with hqb
  have hcomm_N : ∀ k ∈ barIn M K, ⁅k, qb⁆ ∈ N := by
    rintro _ ⟨m, hm, rfl⟩
    have hm : (m : G) ∈ K := hm
    have hc := hqS m hm
    refine ⟨⁅m, ⟨q, hqM⟩⁆, Subgroup.mem_subgroupOf.2 ?_, by rw [map_commutatorElement]⟩
    simpa [commutatorElement_def] using hc
  have hcomm := Thm2Comp.commute_of_commutator_central hperf (q := qb)
    (fun k hk => hNK (hcomm_N k hk)) (fun k hk k' hk' => hNc _ (hcomm_N k hk) k' hk')
  refine (Thm2Comp.mem_CMbar_iff hKM ⟨q, hqM⟩).2 (Subgroup.mem_centralizer_iff.2 fun k hk => ?_)
  exact hcomm k hk

theorem false_of_shape3_L5 (hB : B_B2_g4) {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1 x K M Q H) (h3 : Stage3A x A M H)
    (hL5 : PuL5 ↥(barIn M H)) (k3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  have hKM : K ≤ M := h1.K_le
  have hKH : K ≤ H := h1.H_min.1
  have hbarKH : barIn M K ≤ barIn M H := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hKH hm, rfl⟩
  have hHn : (barIn M H).Normal := by
    rw [h3.H_simple.1]
    exact (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxM : x ∈ M := h3.Cx_le hxC
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  set xb : Mbar M := ρ ⟨x, hxM⟩ with hxb
  have hxH : xb ∈ barIn M H := T4S1.mk_mem_barIn hs h3 hL5 hxM hxx
  have hcomp := Prop31.isCompIn_barIn_centralizer hB hs hxM h3.Cx_le
  have hKq : IsQuasisimple ↥(barIn M K) := Prop31.isQuasisimple_of_isCompIn hcomp
  have hcompH : IsCompIn (barIn M H ⊓ centralizer ({xb} : Set (Mbar M))) (barIn M K) :=
    Prop31.isCompIn_of_le (le_inf hbarKH hcomp.1) inf_le_right hcomp
  have hZK : ∀ z ∈ barIn M K, (∀ l ∈ barIn M K, z * l = l * z) → z * z = 1 → z = 1 := by
    intro z hz hzc hzz
    obtain ⟨Z, hZc, hZo, hZn, ⟨e⟩⟩ := T4ElimAssembly.exists_shape_iso hKM hKq
    have hKt : ∀ w : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * w = w * g) → w = 1 :=
      B1.PilotS3.center_trivial_of_simple_of_quasisimple (B1.PilotS3.isSimpleGroup_of_qShape3 k3)
        (TwoThin.isQuasisimple_hat hs.pair.1.1.1.2.2)
    have himg : (QuotientGroup.mk (⟨z, hz⟩ : ↥(barIn M K)) : ↥(barIn M K) ⧸ Z) = 1 := by
      have h0 := hKt (e.symm (QuotientGroup.mk ⟨z, hz⟩)) (fun g => by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (e g)
        rw [← hw, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (hzc w w.2).symm)
      have := congrArg e h0
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have hzZ : (⟨z, hz⟩ : ↥(barIn M K)) ∈ Z := (QuotientGroup.eq_one_iff _).1 himg
    have hdvd : orderOf (⟨z, hz⟩ : ↥(barIn M K)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact Subtype.ext hzz)
    have hdvd' : orderOf (⟨z, hz⟩ : ↥(barIn M K)) ∣ Nat.card ↥Z := Subgroup.orderOf_dvd_natCard _ hzZ
    have h1' : orderOf (⟨z, hz⟩ : ↥(barIn M K)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hdvd'
        exact absurd (Odd.of_dvd_nat hZo hdvd') (by decide)
    have := orderOf_eq_one_iff.1 h1'
    exact congrArg Subtype.val this
  obtain ⟨-, hAel, hA8, hcase⟩ := hs.src
  have hAK4 : 3 ≤ Nat.card ↥(A ⊓ K) := by
    rcases hcase with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -, -, hE4, -⟩
    · rw [inf_eq_left.2 hAK, hA8]
      norm_num
    · have hEA : E ≤ A := hAE ▸ le_sup_left
      have := Subgroup.card_le_of_le (le_inf hEA hEK)
      omega
  obtain ⟨a, haAK, b, hbAK, ha1, hb1, hab⟩ := exists_two_ne (A ⊓ K) hAK4
  have hsqA : ∀ g ∈ A, g * g = 1 := fun g hg =>
    congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hAel ⟨g, hg⟩)
  have hcommA : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨g, hg⟩ ⟨h, hh⟩)
  set ab : Mbar M := ρ ⟨a, hKM haAK.2⟩ with hab'
  set bb : Mbar M := ρ ⟨b, hKM hbAK.2⟩ with hbb'
  have habK : ab ∈ barIn M K := ⟨⟨a, hKM haAK.2⟩, haAK.2, rfl⟩
  have hbbK : bb ∈ barIn M K := ⟨⟨b, hKM hbAK.2⟩, hbAK.2, rfl⟩
  have haa : ab * ab = 1 := by
    rw [hab', ← map_mul, show (⟨a, hKM haAK.2⟩ : ↥M) * ⟨a, hKM haAK.2⟩ = 1 from
      Subtype.ext (hsqA a haAK.1), map_one]
  have hbbsq : bb * bb = 1 := by
    rw [hbb', ← map_mul, show (⟨b, hKM hbAK.2⟩ : ↥M) * ⟨b, hKM hbAK.2⟩ = 1 from
      Subtype.ext (hsqA b hbAK.1), map_one]
  have hab1 : ab ≠ 1 := mk_ne_one_of_sq (Subtype.ext (hsqA a haAK.1)) (fun h => ha1 (congrArg Subtype.val h))
  have hbb1 : bb ≠ 1 := mk_ne_one_of_sq (Subtype.ext (hsqA b hbAK.1)) (fun h => hb1 (congrArg Subtype.val h))
  have habne : ab ≠ bb := by
    intro h
    have hw : (a * b⁻¹) * (a * b⁻¹) = 1 := by
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsqA b hbAK.1)
      rw [hb']
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcommA b hbAK.1 a haAK.1]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [hsqA a haAK.1, hsqA b hbAK.1, one_mul]
    have hab2 : (⟨a, hKM haAK.2⟩ : ↥M) * ⟨b, hKM hbAK.2⟩⁻¹ * (⟨a, hKM haAK.2⟩ * ⟨b, hKM hbAK.2⟩⁻¹) = 1 :=
      Subtype.ext hw
    have hne1 : (⟨a, hKM haAK.2⟩ : ↥M) * ⟨b, hKM hbAK.2⟩⁻¹ ≠ 1 := by
      intro h'
      apply hab
      have := congrArg Subtype.val h'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
      exact mul_inv_eq_one.1 this
    apply mk_ne_one_of_sq hab2 hne1
    rw [map_mul, map_inv]
    change ab * bb⁻¹ = 1
    rw [h, mul_inv_cancel]
  have habc : ab * bb = bb * ab := by
    rw [hab', hbb', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcommA a haAK.1 b hbAK.1)
  have ha2 : orderOf ab = 2 := orderOf_eq_prime (by rw [sq]; exact haa) hab1
  set J := barIn M H with hJ
  have hfact : B3aFact ↥J := B3aModels.b3aFact_of_puL5 hL5
  set t : ↥J := ⟨xb, hxH⟩ with ht
  have htt : t * t = 1 := by
    apply Subtype.ext
    show xb * xb = 1
    rw [hxb, ← map_mul, show (⟨x, hxM⟩ : ↥M) * ⟨x, hxM⟩ = 1 from Subtype.ext hxx, map_one]
  have hx1 : (⟨x, hxM⟩ : ↥M) ≠ 1 := by
    intro h'
    have hx1' : x = 1 := congrArg Subtype.val h'
    rw [hx1', orderOf_one] at hx2
    omega
  have hxb1 : xb ≠ 1 := mk_ne_one_of_sq (g := ⟨x, hxM⟩) (Subtype.ext hxx) hx1
  have ht1 : t ≠ 1 := fun h => hxb1 (congrArg Subtype.val h)
  set L : Subgroup ↥J := (barIn M K).subgroupOf J with hL
  have hLmap : L.map J.subtype = barIn M K := Subgroup.map_subgroupOf_eq_of_le hbarKH
  have hLcomp : IsCompIn (centralizer ({t} : Set ↥J)) L := by
    refine isCompIn_of_map_injective J.subtype_injective ?_
    rw [map_subtype_centralizer, hLmap]
    exact hcompH
  have hZL : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z * z = 1 → z = 1 := by
    intro z hz hzc hzz
    apply Subtype.ext
    refine hZK (z : Mbar M) (Subgroup.mem_subgroupOf.1 hz) (fun l hl => ?_) (congrArg Subtype.val hzz)
    exact congrArg Subtype.val (hzc ⟨l, hbarKH hl⟩ (Subgroup.mem_subgroupOf.2 hl))
  have h4L : ∃ a ∈ L, ∃ b ∈ L, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a :=
    ⟨⟨ab, hbarKH habK⟩, Subgroup.mem_subgroupOf.2 habK, ⟨bb, hbarKH hbbK⟩, Subgroup.mem_subgroupOf.2 hbbK,
      Subtype.ext haa, Subtype.ext hbbsq, fun h => hab1 (congrArg Subtype.val h),
      fun h => hbb1 (congrArg Subtype.val h), fun h => habne (congrArg Subtype.val h), Subtype.ext habc⟩
  obtain ⟨e, hee, he1, hec, L', hL', hLL', hne⟩ := hfact t htt ht1 L hLcomp hZL h4L
  have hecent : (e : Mbar M) ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) := by
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    have := hec ⟨k, hbarKH hk⟩ (Subgroup.mem_subgroupOf.2 hk)
    exact (congrArg Subtype.val this).symm
  obtain ⟨g₀, hg₀sq, hg₀⟩ := exists_invol_lift (M := M) (z := (e : Mbar M)) (congrArg Subtype.val hee)
  have he₀C : (g₀ : G) ∈ CMbar M K := (Thm2Comp.mem_CMbar_iff hKM g₀).2 (by rw [hg₀]; exact hecent)
  have hQC : Q ≤ CMbar M K := Q_le_CMbar_of_barK hs h1 hKq habK ha2
  have hQsyl : IsSylowOf 2 Q (CMbar M K) := isSylowOf_CMbar_of_le hs hKM hQC
  obtain ⟨c, hcX, hcQ⟩ := Stage2.Final.Thm6.L20.exists_mem_conj_into_sylow hQsyl he₀C
    (congrArg Subtype.val hg₀sq)
  set y : G := c * (g₀ : G) * c⁻¹ with hy
  have hcM : c ∈ M := hcX.1
  have hyM : y ∈ M := h1.Q_le hcQ
  have hyC : y ∈ CxK x K := hs.sylowQ.le hcQ
  have hyy : y * y = 1 := by
    calc y * y = c * ((g₀ : G) * (g₀ : G)) * c⁻¹ := by rw [hy]; group
      _ = 1 := by rw [show (g₀ : G) * (g₀ : G) = 1 from congrArg Subtype.val hg₀sq]; group
  set cb : Mbar M := ρ ⟨c, hcM⟩ with hcb
  have hyb : ρ ⟨y, hyM⟩ = cb * (e : Mbar M) * cb⁻¹ := by
    have : (⟨y, hyM⟩ : ↥M) = ⟨c, hcM⟩ * g₀ * ⟨c, hcM⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hg₀]
  have hy1 : y ≠ 1 := by
    intro h
    apply he1
    apply Subtype.ext
    have h' : ρ ⟨y, hyM⟩ = 1 := by
      rw [show (⟨y, hyM⟩ : ↥M) = 1 from Subtype.ext h, map_one]
    rw [hyb] at h'
    have : (e : Mbar M) = cb⁻¹ * (cb * (e : Mbar M) * cb⁻¹) * cb := by group
    rw [this, h']
    simp
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  have hycent : ρ ⟨y, hyM⟩ ∈ centralizer ((barIn M K : Subgroup (Mbar M)) : Set (Mbar M)) := (Thm2Comp.mem_CMbar_iff hKM ⟨y, hyM⟩).1 (hQC hcQ)
  have hKy : IsCompIn (centralizer ({ρ ⟨y, hyM⟩} : Set (Mbar M))) (barIn M K) :=
    barIn_K_isCompIn_at hB hs.hyp hs.maxM.1 hs.pair.1.1.1 hs.pair.1.2.2 hKM hKq hyC hy2 hyM hycent
  have hcbK : ∀ k ∈ barIn M K, cb * k * cb⁻¹ = k := by
    intro k hk
    have hc := (Thm2Comp.mem_CMbar_iff hKM ⟨c, hcM⟩).1 hcX
    have := Subgroup.mem_centralizer_iff.1 hc k hk
    rw [← hcb] at this
    calc cb * k * cb⁻¹ = (k * cb) * cb⁻¹ := by rw [this]
      _ = k := by group
  set φ : MulAut ↥J := MulAut.conjNormal cb with hφ
  have hφa : ∀ j : ↥J, ((φ j : ↥J) : Mbar M) = cb * (j : Mbar M) * cb⁻¹ := fun j => by
    simp [hφ, MulAut.conjNormal_apply]
  have hφe : ((φ e : ↥J) : Mbar M) = ρ ⟨y, hyM⟩ := by rw [hφa, hyb]
  have hL'' : IsCompIn (centralizer ({φ e} : Set ↥J)) (L'.map φ.toMonoidHom) := by
    rw [← centralizer_map_mulEquiv]
    exact isCompIn_map φ hL'
  have hL''M : IsCompIn ((centralizer ({φ e} : Set ↥J)).map J.subtype) ((L'.map φ.toMonoidHom).map J.subtype) :=
    isCompIn_map_of_injective J.subtype_injective hL''
  rw [map_subtype_centralizer] at hL''M
  have hφeJ : ((φ e : ↥J) : Mbar M) = ρ ⟨y, hyM⟩ := hφe
  rw [hφeJ] at hL''M
  have hL''C : IsCompIn (centralizer ({ρ ⟨y, hyM⟩} : Set (Mbar M))) ((L'.map φ.toMonoidHom).map J.subtype) :=
    CFSG.GH74.GLS.LU.Local.isCompIn_of_normal hL''M inf_le_right (fun g hg a ha =>
      ⟨hHn.conj_mem a ha.1 g, (centralizer _).mul_mem ((centralizer _).mul_mem hg ha.2)
        ((centralizer _).inv_mem hg)⟩)
  have hφL : L.map φ.toMonoidHom = L := by
    ext j
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : (w : Mbar M) ∈ barIn M K := Subgroup.mem_subgroupOf.1 hw
      refine Subgroup.mem_subgroupOf.2 ?_
      show ((φ w : ↥J) : Mbar M) ∈ barIn M K
      rw [hφa, hcbK _ hw']
      exact hw'
    · intro hj
      have hj' : (j : Mbar M) ∈ barIn M K := Subgroup.mem_subgroupOf.1 hj
      refine ⟨j, hj, ?_⟩
      apply Subtype.ext
      show ((φ j : ↥J) : Mbar M) = j
      rw [hφa, hcbK _ hj']
  have hKle : barIn M K ≤ (L'.map φ.toMonoidHom).map J.subtype := by
    rw [← hLmap, ← hφL]
    exact Subgroup.map_mono (Subgroup.map_mono hLL')
  have heq := eq_of_isCompIn_le hKy hL''C hKle
  apply hne
  have h1' : L = L'.map φ.toMonoidHom := by
    apply Subgroup.map_injective J.subtype_injective
    rw [hLmap]
    exact heq
  have h2' : L'.map φ.toMonoidHom = L.map φ.toMonoidHom := by rw [hφL, ← h1']
  exact (Subgroup.map_injective φ.injective h2').symm

theorem notShape3L5_of (hB : B_B2_g4) :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
      Stage2Concl1 x K M Q H → Stage3A x A M H → PuL5 ↥(barIn M H) →
        QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → False :=
  fun _ _ _ _ _ _ _ _ _ _ hs h1 h3 hL5 k3 => false_of_shape3_L5 hB hs h1 h3 hL5 k3

end Group

end CFSG.GH74.Generic.BProg.B2.T4.B3aG
