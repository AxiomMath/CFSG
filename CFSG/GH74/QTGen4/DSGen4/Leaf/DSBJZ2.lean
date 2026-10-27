module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBJZ2

variable {G : Type} [Group G]

theorem omega_le_of_inv {X K : Subgroup G} (h : ∀ x ∈ X, x ^ 2 = 1 → x ∈ K) :
    dsOmega1 X ≤ K := by
  unfold dsOmega1
  exact (Subgroup.closure_le K).2 fun _ hx => h _ hx.1 hx.2

theorem mem_omega_of {X : Subgroup G} {x : G} (hx : x ∈ X) (hx2 : x ^ 2 = 1) :
    x ∈ dsOmega1 X := by
  unfold dsOmega1
  exact Subgroup.subset_closure ⟨hx, hx2⟩

theorem mem_centerOf_iff {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem centerOf_le (X : Subgroup G) : centerOf X ≤ X :=
  fun _ hx => (mem_centerOf_iff.mp hx).1

theorem omega_centerOf_le (X : Subgroup G) : dsOmega1 (centerOf X) ≤ centerOf X :=
  omega_le_of_inv fun _ hx _ => hx

theorem le_normalizer_of_conj {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this

theorem comm_sup {A B : Subgroup G} {x : G} (hA : ∀ a ∈ A, a * x = x * a)
    (hB : ∀ b ∈ B, b * x = x * b) : ∀ s ∈ A ⊔ B, s * x = x * s := by
  have hC : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hA a ha).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hB b hb).symm
  intro s hs
  exact ((Subgroup.mem_centralizer_iff.mp (hC hs)) x rfl).symm

theorem isPGroup_two_of_sq {X : Subgroup G} (h : ∀ x ∈ X, x ^ 2 = 1) : IsPGroup 2 X := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using h x x.2

theorem dsConjClosure_le' {Y X K : Subgroup G} (h : ∀ y ∈ Y, ∀ z ∈ X, y * z * y⁻¹ ∈ K) :
    dsConjClosure Y X ≤ K := by
  unfold dsConjClosure
  refine iSup₂_le fun y hy => ?_
  rintro _ ⟨z, hz, rfl⟩
  exact h y hy z hz

theorem conj_mem_dsConjClosure {Y X : Subgroup G} {y z : G} (hy : y ∈ Y) (hz : z ∈ X) :
    y * z * y⁻¹ ∈ dsConjClosure Y X := by
  have hmem : y * z * y⁻¹ ∈ X.map (MulAut.conj y).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hle : X.map (MulAut.conj y).toMonoidHom ≤ dsConjClosure Y X :=
    le_iSup₂ (f := fun w (_ : w ∈ Y) => X.map (MulAut.conj w).toMonoidHom) y hy
  exact hle hmem

theorem comm_of_cJ {L1 S : Subgroup G} (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) {z : G}
    (hz : z ∈ dsZi L1 S) : ∀ l ∈ L1, l * z = z * l := by
  intro l hl
  have hc : ⁅z, l⁆ ∈ (⊥ : Subgroup G) := by
    rw [← cJ]
    exact Subgroup.commutator_mem_commutator hz hl
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc.symm

theorem le_normalizer_bot (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
  le_normalizer_of_conj fun g _ x hx => by
    rw [Subgroup.mem_bot] at hx ⊢
    simp [hx]

theorem s3_comm_inv : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
    a * b * a⁻¹ * b = 1 := by decide

theorem s3_decomp : ∀ a b x : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
    ∃ i < 3, ∃ j < 2, x = b ^ i * a ^ j := by decide

theorem s3_pow_six : ∀ x : Equiv.Perm (Fin 3), x ^ 6 = 1 := by decide

theorem s3_gcd_six_dvd (n : ℕ) : Nat.gcd 6 (2 ^ n) ∣ 2 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Nat.gcd_dvd_right 6 (2 ^ n))
  have h6 : 2 ^ j ∣ 6 := by rw [← hj]; exact Nat.gcd_dvd_left 6 (2 ^ n)
  rw [hj]
  rcases Nat.lt_or_ge j 2 with hlt | hge
  · simpa using pow_dvd_pow 2 (show j ≤ 1 by omega)
  · exact absurd (dvd_trans (pow_dvd_pow 2 hge) h6) (by norm_num)

theorem s3_sq_of_pow_two {x : Equiv.Perm (Fin 3)} {n : ℕ} (h : x ^ 2 ^ n = 1) : x ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := s3_gcd_six_dvd n
  have hg : x ^ Nat.gcd 6 (2 ^ n) = 1 := pow_gcd_eq_one.mpr ⟨s3_pow_six x, h⟩
  calc x ^ 2 = x ^ (Nat.gcd 6 (2 ^ n) * c) := by rw [← hc]
    _ = 1 := by rw [pow_mul, hg, one_pow]


theorem j1 [Finite4 G] [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafSylowS] [DSLeaf LeafZiStructure]
    [DSLeaf LeafFrattiniChief] [DSLeaf LeafFaithfulA5] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S)
    (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    dsOmega1 (centerOf (dsQ L1 L2 S)) = dsZ S ∧ dsZ S ≤ dsFrattini (dsQ L1 L2 S) := by
  have hyp : Hyp111R L1 L2 S := h.hyp
  have hA : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 hyp h.ns1
  have hZS : ZSetting L1 L2 S := ⟨hyp, DSBHyp.bnorm h⟩
  obtain ⟨hZne, hZZi, hZY, hYel, hYcard, hPZ, hPY⟩ := zi_structure hZS
  obtain ⟨hd5S, -, hd5Q⟩ := dsba5_vertex h
  have hQS : dsQ L1 L2 S ≤ S := (sylow_s hyp).2.2
  have hchief : A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S) (dsFrattini (dsQ L1 L2 S)) :=
    frattini_chief hA
  have hZi : dsZi L1 S = dsZ S := dsZi_eq_dsZ_of_commutator_eq_bot cJ
  have hZY' : dsZ S ≤ dsOmega1 (centerOf (dsQ L1 L2 S)) := hZZi.trans hZY
  have hY1Q : dsOmega1 (centerOf (dsQ L1 L2 S)) ≤ dsQ L1 L2 S :=
    (omega_centerOf_le _).trans (centerOf_le _)
  have hQP : dsQ L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hY1P : dsOmega1 (centerOf (dsQ L1 L2 S)) ≤ L1 ⊔ bigB L1 L2 S := hY1Q.trans hQP
  have hZQ : dsZ S ≤ dsQ L1 L2 S := hZY'.trans hY1Q
  have hY1comm : ∀ l ∈ L1, ∀ y ∈ dsOmega1 (centerOf (dsQ L1 L2 S)), l * y = y * l := by
    by_contra hne
    simp only [not_forall, not_imp] at hne
    obtain ⟨l, hl, y, hy, hly⟩ := hne
    have hel : IsElemSec (⊥ : Subgroup G) (dsOmega1 (centerOf (dsQ L1 L2 S))) := by
      refine ⟨bot_le, ?_, fun e he => ?_⟩
      · rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact F7.isElemAbelian_comm hYel ha hb
      · rw [Subgroup.mem_bot]
        exact hYel.2 e he
    have hcard : (⊥ : Subgroup G).relIndex (dsOmega1 (centerOf (dsQ L1 L2 S))) ≤ 16 := by
      rw [Subgroup.relIndex_bot_left]
      exact hYcard
    have hcore : ∀ q ∈ pCoreOf 2 (L1 ⊔ bigB L1 L2 S), ∀ e ∈ dsOmega1 (centerOf (dsQ L1 L2 S)),
        ⁅q, e⁆ ∈ (⊥ : Subgroup G) := by
      intro q hq e he
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centerOf_iff.mp (omega_centerOf_le _ he)).2 q hq
    have hnt : ∃ l ∈ L1, ∃ e ∈ dsOmega1 (centerOf (dsQ L1 L2 S)), ⁅l, e⁆ ∉ (⊥ : Subgroup G) :=
      ⟨l, hl, y, hy, fun h1 => hly (commutatorElement_eq_one_iff_mul_comm.mp
        (Subgroup.mem_bot.mp h1))⟩
    have hA5 : A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsOmega1 (centerOf (dsQ L1 L2 S))) ⊥ :=
      faithful_a5 le_sup_left hA.norm hY1P hPY (le_normalizer_bot _) hel hcard hA.quot hcore hnt
    have hXnorm : (L1 ⊔ bigB L1 L2 S) ≤ Subgroup.normalizer
        ((dsOmega1 (centerOf (dsQ L1 L2 S)) ⊓ Subgroup.centralizer (L1 : Set G) : Subgroup G) :
          Set G) := by
      refine le_normalizer_of_conj fun p hp x hx => ?_
      obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hPY hp) x).mp hxY, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : p⁻¹ * l * p ∈ L1 := by
        have := (Subgroup.mem_normalizer_iff.mp (hA.norm (Subgroup.inv_mem _ hp)) l).mp hl
        rwa [inv_inv] at this
      have hc := (Subgroup.mem_centralizer_iff.mp hxC) (p⁻¹ * l * p) hl'
      calc l * (p * x * p⁻¹) = p * ((p⁻¹ * l * p) * x) * p⁻¹ := by group
        _ = p * (x * (p⁻¹ * l * p)) * p⁻¹ := by rw [hc]
        _ = p * x * p⁻¹ * l := by group
    rcases hA5.irred _ bot_le inf_le_left hXnorm with hX0 | hXY
    · have hZC : dsZ S ≤ (⊥ : Subgroup G) := by
        intro z hz
        have hzC : z ∈ Subgroup.centralizer (L1 : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun l hl => comm_of_cJ cJ (hZZi hz) l hl
        have hz' : z ∈ dsOmega1 (centerOf (dsQ L1 L2 S)) ⊓ Subgroup.centralizer (L1 : Set G) :=
          Subgroup.mem_inf.mpr ⟨hZY' hz, hzC⟩
        rw [hX0] at hz'
        exact hz'
      exact hZne (le_bot_iff.mp hZC)
    · have hyC : y ∈ dsOmega1 (centerOf (dsQ L1 L2 S)) ⊓ Subgroup.centralizer (L1 : Set G) := by
        rw [hXY]
        exact hy
      exact hly ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyC).2) l hl)
  have hY1Z : dsOmega1 (centerOf (dsQ L1 L2 S)) ≤ dsZ S := by
    refine omega_le_of_inv fun x hx hx2 => ?_
    have hxQ : x ∈ dsQ L1 L2 S := centerOf_le _ hx
    have key := comm_sup (A := S ⊓ L1) (B := dsQ L1 L2 S) (x := x)
      (fun a ha => hY1comm a (Subgroup.mem_inf.mp ha).2 x (mem_omega_of hx hx2))
      (fun b hb => (mem_centerOf_iff.mp hx).2 b hb)
    rw [← hd5S] at key
    exact mem_omega_of (mem_centerOf_iff.mpr ⟨hQS hxQ, key⟩) hx2
  have hZΦ : dsZ S ≤ dsFrattini (dsQ L1 L2 S) := by
    have hΦQ : dsFrattini (dsQ L1 L2 S) ≤ dsQ L1 L2 S := Subgroup.map_subtype_le _
    have hZN : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsZ S : Set G) := by
      have := hPZ
      rw [hZi] at this
      exact this
    have hPX := F1.le_normalizer_sup hchief.norm_K hZN
    have hXQ : dsFrattini (dsQ L1 L2 S) ⊔ dsZ S ≤ dsQ L1 L2 S := sup_le hΦQ hZQ
    rcases hchief.irred _ le_sup_left hXQ hPX with hXΦ | hXQ1
    · exact (le_sup_right : dsZ S ≤ dsFrattini (dsQ L1 L2 S) ⊔ dsZ S).trans hXΦ.le
    · exfalso
      let C : Subgroup G := dsCentMod (L1 ⊔ bigB L1 L2 S) L1 (dsFrattini (dsQ L1 L2 S))
      have hΦC : dsFrattini (dsQ L1 L2 S) ≤ C := by
        intro φ hφ
        have hφP : φ ∈ L1 ⊔ bigB L1 L2 S := hQP (hΦQ hφ)
        refine ⟨hφP, Subgroup.le_normalizer hφ, fun l hl => ?_⟩
        have hconj : l * φ⁻¹ * l⁻¹ ∈ dsFrattini (dsQ L1 L2 S) :=
          (Subgroup.mem_normalizer_iff.mp (hchief.norm_K (hA.le hl)) φ⁻¹).mp
            (Subgroup.inv_mem _ hφ)
        rw [commutatorElement_def]
        have e : φ * l * φ⁻¹ * l⁻¹ = φ * (l * φ⁻¹ * l⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hφ hconj
      have hZC : dsZ S ≤ C := by
        intro z hz
        have hzP : z ∈ L1 ⊔ bigB L1 L2 S := hQP (hZQ hz)
        refine ⟨hzP, hchief.norm_K hzP, fun l hl => ?_⟩
        have hc1 : ⁅z, l⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (comm_of_cJ cJ (hZZi hz) l hl).symm
        rw [hc1]
        exact Subgroup.one_mem _
      have hQC : dsQ L1 L2 S ≤ C := by
        have := sup_le hΦC hZC
        rw [hXQ1] at this
        exact this
      obtain ⟨l, hl, e, he, hle⟩ := hchief.nontriv
      have hec := (hQC he).2.2 l hl
      apply hle
      have hinv : ⁅l, e⁆ = ⁅e, l⁆⁻¹ := by rw [commutatorElement_inv]
      rw [hinv]
      exact Subgroup.inv_mem _ hec
  exact ⟨le_antisymm hY1Z hZY', hZΦ⟩


theorem mem_pCoreOf_iff {L : Subgroup G} (g : ↥L) :
    (g : G) ∈ pCoreOf 2 L ↔ g ∈ CFSG.Open.pCore 2 ↥L := by
  constructor
  · intro hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
    have hyg' : y = g := Subtype.ext hyg
    exact hyg' ▸ hy
  · intro hg
    exact Subgroup.mem_map_of_mem _ hg

@[expose] noncomputable def s3Hom (L : Subgroup G) (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) :
    ↥L →* Equiv.Perm (Fin 3) :=
  haveI : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L))

theorem s3Hom_apply {L : Subgroup G} (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) (g : ↥L) :
    s3Hom L e g = e (QuotientGroup.mk g) := rfl

theorem s3Hom_eq_one_iff {L : Subgroup G} (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) (g : ↥L) :
    s3Hom L e g = 1 ↔ (g : G) ∈ pCoreOf 2 L := by
  haveI : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  rw [s3Hom_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  exact (mem_pCoreOf_iff g).symm

theorem not_mem_pCoreOf_of_orderOf [Finite G] {L : Subgroup G} {k : G} (hk : k ∈ L)
    (hk3 : orderOf k = 3) : k ∉ pCoreOf 2 L := by
  intro hmem
  have hp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  obtain ⟨n, hn⟩ := hp ⟨k, hmem⟩
  have hkn : k ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hdvd : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hkn
  rw [hk3] at hdvd
  have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h3

theorem s3Hom_sq_eq_one {L : Subgroup G} (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) {t : G}
    (ht : t ∈ L) (ht2 : t ^ 2 ∈ pCoreOf 2 L) : s3Hom L e ⟨t, ht⟩ ^ 2 = 1 := by
  rw [← map_pow, s3Hom_eq_one_iff]
  have hval : ((⟨t, ht⟩ ^ 2 : ↥L) : G) = t ^ 2 := by simp
  rw [hval]
  exact ht2

theorem s3Hom_three_eq_one {L : Subgroup G} (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) {k : G}
    (hk : k ∈ L) (hk3 : orderOf k = 3) : s3Hom L e ⟨k, hk⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have hKo : orderOf (⟨k, hk⟩ : ↥L) = 3 := by rw [Subgroup.orderOf_mk, hk3]
  have : (⟨k, hk⟩ : ↥L) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (⟨k, hk⟩ : ↥L)
    rwa [hKo] at this
  rw [this, map_one]

theorem s3_rel {L : Subgroup G} [Finite G] (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) {t k : G}
    (ht : t ∈ L) (hk : k ∈ L) (ht1 : t ∉ pCoreOf 2 L) (ht2 : t ^ 2 ∈ pCoreOf 2 L)
    (hk3 : orderOf k = 3) : t * k * t⁻¹ * k ∈ pCoreOf 2 L := by
  have hk1 : k ∉ pCoreOf 2 L := not_mem_pCoreOf_of_orderOf hk hk3
  have hT2 : s3Hom L e ⟨t, ht⟩ ^ 2 = 1 := s3Hom_sq_eq_one e ht ht2
  have hT1 : s3Hom L e ⟨t, ht⟩ ≠ 1 := fun h1 => ht1 ((s3Hom_eq_one_iff e ⟨t, ht⟩).mp h1)
  have hK3 : s3Hom L e ⟨k, hk⟩ ^ 3 = 1 := s3Hom_three_eq_one e hk hk3
  have hK1 : s3Hom L e ⟨k, hk⟩ ≠ 1 := fun h1 => hk1 ((s3Hom_eq_one_iff e ⟨k, hk⟩).mp h1)
  have hU : s3Hom L e (⟨t, ht⟩ * ⟨k, hk⟩ * ⟨t, ht⟩⁻¹ * ⟨k, hk⟩) = 1 := by
    simp only [map_mul, map_inv]
    exact s3_comm_inv _ _ (by rwa [sq] at hT2) hT1 hK3 hK1
  have hval : ((⟨t, ht⟩ * ⟨k, hk⟩ * ⟨t, ht⟩⁻¹ * ⟨k, hk⟩ : ↥L) : G) = t * k * t⁻¹ * k := rfl
  rw [← hval]
  exact (s3Hom_eq_one_iff e _).mp hU

theorem s3_decomp_mem {L : Subgroup G} [Finite G] (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) {t k : G}
    (ht : t ∈ L) (hk : k ∈ L) (ht1 : t ∉ pCoreOf 2 L) (ht2 : t ^ 2 ∈ pCoreOf 2 L)
    (hk3 : orderOf k = 3) {g : G} (hg : g ∈ L) :
    ∃ i < 3, ∃ j < 2, ∃ o ∈ pCoreOf 2 L, g = k ^ i * t ^ j * o := by
  have hk1 : k ∉ pCoreOf 2 L := not_mem_pCoreOf_of_orderOf hk hk3
  have hT2 : s3Hom L e ⟨t, ht⟩ ^ 2 = 1 := s3Hom_sq_eq_one e ht ht2
  have hT1 : s3Hom L e ⟨t, ht⟩ ≠ 1 := fun h1 => ht1 ((s3Hom_eq_one_iff e ⟨t, ht⟩).mp h1)
  have hK3 : s3Hom L e ⟨k, hk⟩ ^ 3 = 1 := s3Hom_three_eq_one e hk hk3
  have hK1 : s3Hom L e ⟨k, hk⟩ ≠ 1 := fun h1 => hk1 ((s3Hom_eq_one_iff e ⟨k, hk⟩).mp h1)
  obtain ⟨i, hi, j, hj, hx⟩ := s3_decomp (s3Hom L e ⟨t, ht⟩) (s3Hom L e ⟨k, hk⟩)
    (s3Hom L e ⟨g, hg⟩) (by rwa [sq] at hT2) hT1 hK3 hK1
  set o : ↥L := ((⟨k, hk⟩ : ↥L) ^ i * (⟨t, ht⟩ : ↥L) ^ j)⁻¹ * ⟨g, hg⟩ with ho_def
  have hho : s3Hom L e o = 1 := by
    rw [ho_def, map_mul, map_inv, map_mul, map_pow, map_pow, ← hx, inv_mul_cancel]
  have hval2 : (((⟨k, hk⟩ : ↥L) ^ i * (⟨t, ht⟩ : ↥L) ^ j : ↥L) : G) = k ^ i * t ^ j := by
    simp
  refine ⟨i, hi, j, hj, (o : G), (s3Hom_eq_one_iff e o).mp hho, ?_⟩
  have hgo : (o : G) = ((⟨k, hk⟩ : ↥L) ^ i * (⟨t, ht⟩ : ↥L) ^ j)⁻¹ * g := rfl
  rw [hgo, ← hval2, Subgroup.coe_inv, mul_inv_cancel_left]

theorem exists_order3 [Finite G] {L : Subgroup G} (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) :
    ∃ k ∈ L, orderOf k = 3 := by
  haveI : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hcard : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (CFSG.Open.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hq6 : Nat.card (oTwoQuot ↥L) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h3 : 3 ∣ Nat.card ↥L := by
    rw [hcard, hq6]
    exact Dvd.intro (Nat.card (CFSG.Open.pCore 2 ↥L) * 2) (by ring)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩


theorem exists_t [Finite4 G] [DSLeaf LeafSylowS] [DSLeaf LeafDSBS3Vertex] {L1 L2 S : Subgroup G}
    (h : DSBHyp L1 L2 S) :
    ∃ t ∈ S ⊓ L2, t ∉ dsQ L2 L1 S ∧ t ^ 2 ∈ pCoreOf 2 L2 := by
  have hyp2 : Hyp111R L2 L1 S := h.hyp.symm
  obtain ⟨hd3, hrel, -, -⟩ := dsbs3_vertex h
  have hQS : dsQ L2 L1 S ≤ S := (sylow_s hyp2).2.2
  have hsex : ∃ s ∈ S, s ∉ dsQ L2 L1 S := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hEq : S = dsQ L2 L1 S := le_antisymm (fun s hs => hcon s hs) hQS
    have hrel1 : (dsQ L2 L1 S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hEq.le
    rw [hrel1] at hrel
    norm_num at hrel
  obtain ⟨s, hsS, hsQ⟩ := hsex
  have hN : S ⊓ L2 ≤ Subgroup.normalizer ((dsQ L2 L1 S : Subgroup G) : Set G) :=
    inf_le_right.trans (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hs' : s ∈ (S ⊓ L2) ⊔ dsQ L2 L1 S := by
    rw [← hd3]
    exact hsS
  obtain ⟨a, ha, b, hb, hsab⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hN).mp hs'
  have haQ : a ∉ dsQ L2 L1 S := fun haQ => hsQ (hsab ▸ Subgroup.mul_mem _ haQ hb)
  have haL : a ∈ L2 := (Subgroup.mem_inf.mp ha).2
  obtain ⟨n, hn⟩ := (h.hyp.hyp.h2.sylow).2.1 ⟨a, ha⟩
  have hApow : (⟨a, haL⟩ : ↥L2) ^ 2 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨e⟩ := h.s3
  have hsq : s3Hom L2 e ⟨a, haL⟩ ^ 2 = 1 := by
    apply s3_sq_of_pow_two (n := n)
    rw [← map_pow, hApow, map_one]
  have hmem : s3Hom L2 e (⟨a, haL⟩ ^ 2) = 1 := by
    rw [map_pow]
    exact hsq
  refine ⟨a, ha, haQ, ?_⟩
  have := (s3Hom_eq_one_iff e _).mp hmem
  simpa using this

theorem c_L2 [Finite4 G] [DSLeaf LeafZiStructure] [DSLeaf LeafSylowS] [DSLeaf LeafDSBS3Vertex]
    {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) {y : G}
    (hy : y ∈ dsOmega1 (centerOf (dsQ L2 L1 S))) (hcomm : ∀ g ∈ L2, g * y = y * g) : y = 1 := by
  have hyp2 : Hyp111R L2 L1 S := h.hyp.symm
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, DSBHyp.bnorm h⟩
  have hZi : dsZi L1 S = dsZ S := dsZi_eq_dsZ_of_commutator_eq_bot cJ
  obtain ⟨-, hZZ2, hZY2, hY2el, -, -, -⟩ := zi_structure hZS.symm
  have hQ2S : dsQ L2 L1 S ≤ S := (sylow_s hyp2).2.2
  obtain ⟨hd3, -, -, -⟩ := dsbs3_vertex h
  have hZY : dsZ S ≤ dsOmega1 (centerOf (dsQ L2 L1 S)) := hZZ2.trans hZY2
  have hFZ : ∀ f ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G),
      f ∈ dsZ S := by
    intro f hf
    obtain ⟨hfY, hfC⟩ := Subgroup.mem_inf.mp hf
    have hfC' : ∀ g ∈ L2, g * f = f * g := fun g hg => Subgroup.mem_centralizer_iff.mp hfC g hg
    have hfc2 : f ∈ centerOf (dsQ L2 L1 S) := omega_centerOf_le _ hfY
    have hfS : f ∈ S := hQ2S (centerOf_le _ hfc2)
    have key := comm_sup (A := S ⊓ L2) (B := dsQ L2 L1 S) (x := f)
      (fun a ha => hfC' a (Subgroup.mem_inf.mp ha).2)
      (fun b hb => (mem_centerOf_iff.mp hfc2).2 b hb)
    rw [← hd3] at key
    exact mem_omega_of (mem_centerOf_iff.mpr ⟨hfS, key⟩) (hY2el.2 f hfY)
  have hFbot : dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) = ⊥ := by
    have hFel : IsPGroup 2 (dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) :
        Subgroup G) :=
      isPGroup_two_of_sq fun f hf => hY2el.2 f (Subgroup.mem_inf.mp hf).1
    have hFle : dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) ≤
        L1 ⊔ L2 ⊔ S := fun f hf =>
      (le_sup_right : S ≤ L1 ⊔ L2 ⊔ S) (centerOf_le S (dsZ_le_center S (hFZ f hf)))
    have h1 : L1 ≤ Subgroup.normalizer
        ((dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) : Subgroup G) :
          Set G) := by
      refine le_normalizer_of_conj fun g hg f hf => ?_
      have hfZ := hFZ f hf
      have hfZ1 : f ∈ dsZi L1 S := by
        rw [hZi]
        exact hfZ
      have hgf : g * f = f * g := comm_of_cJ cJ hfZ1 g hg
      have e1 : g * f * g⁻¹ = f := by rw [hgf, mul_inv_cancel_right]
      rw [e1]
      exact hf
    have h2 : L2 ≤ Subgroup.normalizer
        ((dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) : Subgroup G) :
          Set G) := by
      refine le_normalizer_of_conj fun g hg f hf => ?_
      have hgf : g * f = f * g := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hf).2) g hg
      have e1 : g * f * g⁻¹ = f := by rw [hgf, mul_inv_cancel_right]
      rw [e1]
      exact hf
    have hS : S ≤ Subgroup.normalizer
        ((dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) : Subgroup G) :
          Set G) := by
      refine le_normalizer_of_conj fun g hg f hf => ?_
      have hfZ := hFZ f hf
      have hsf : g * f = f * g := (mem_centerOf_iff.mp (dsZ_le_center S hfZ)).2 g hg
      have e1 : g * f * g⁻¹ = f := by rw [hsf, mul_inv_cancel_right]
      rw [e1]
      exact hf
    exact coreFree h.hyp.hyp hFel hFle h1 h2 hS
  have hyF : y ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) :=
    Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_iff.mpr hcomm⟩
  rw [hFbot] at hyF
  exact Subgroup.mem_bot.mp hyF

theorem fix_centralizes [Finite G] {L2 : Subgroup G} (e : oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3))
    {t k y₀ : G} (ht : t ∈ L2) (hk : k ∈ L2) (ht1 : t ∉ pCoreOf 2 L2) (ht2 : t ^ 2 ∈ pCoreOf 2 L2)
    (hk3 : orderOf k = 3) (hkc : k * y₀ = y₀ * k) (htc : t * y₀ * t⁻¹ = y₀)
    (hcen : ∀ o ∈ pCoreOf 2 L2, o * y₀ = y₀ * o) : ∀ g ∈ L2, g * y₀ = y₀ * g := by
  intro g hg
  obtain ⟨i, -, j, -, o, ho, hgo⟩ := s3_decomp_mem e ht hk ht1 ht2 hk3 hg
  have htc' : t * y₀ = y₀ * t := by
    calc t * y₀ = (t * y₀ * t⁻¹) * t := by group
      _ = y₀ * t := by rw [htc]
  have hck : Commute (k ^ i) y₀ := (show Commute k y₀ from hkc).pow_left i
  have hct : Commute (t ^ j) y₀ := (show Commute t y₀ from htc').pow_left j
  have hco : Commute o y₀ := hcen o ho
  have hall : Commute (k ^ i * t ^ j * o) y₀ := (hck.mul_left hct).mul_left hco
  rw [hgo]
  exact hall.eq

theorem c_k [Finite4 G] [DSLeaf LeafZiStructure] [DSLeaf LeafSylowS] [DSLeaf LeafDSBS3Vertex]
    {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S) (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) {k : G}
    (hk : k ∈ L2) (hk3 : orderOf k = 3) {y : G}
    (hy : y ∈ dsOmega1 (centerOf (dsQ L2 L1 S))) (hcomm : k * y = y * k) : y = 1 := by
  by_contra hy1
  have hyp2 : Hyp111R L2 L1 S := h.hyp.symm
  have hZS2 : ZSetting L2 L1 S := ZSetting.symm ⟨h.hyp, DSBHyp.bnorm h⟩
  obtain ⟨-, -, -, hY2el, -, -, hP2Y⟩ := zi_structure hZS2
  obtain ⟨t, htS, htQ, ht2⟩ := exists_t h
  have htL : t ∈ L2 := (Subgroup.mem_inf.mp htS).2
  obtain ⟨e⟩ := h.s3
  have hO2Q : pCoreOf 2 L2 ≤ dsQ L2 L1 S := F1.pCoreOf_le_pCoreOf_parabolic hyp2
  have ht1 : t ∉ pCoreOf 2 L2 := fun h1 => htQ (hO2Q h1)
  have hu : t * k * t⁻¹ * k ∈ pCoreOf 2 L2 := s3_rel e htL hk ht1 ht2 hk3
  have hcenQ : ∀ q ∈ dsQ L2 L1 S, ∀ w ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
      q * w = w * q := fun q hq w hw => (mem_centerOf_iff.mp (omega_centerOf_le _ hw)).2 q hq
  have hcenO : ∀ o ∈ pCoreOf 2 L2, ∀ w ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
      o * w = w * o := fun o ho w hw => hcenQ o (hO2Q ho) w hw
  have hwY : t * y * t⁻¹ ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) :=
    (Subgroup.mem_normalizer_iff.mp (hP2Y ((le_sup_left : L2 ≤ L2 ⊔ bigB L2 L1 S) htL)) y).mp hy
  set w := t * y * t⁻¹ with hw
  have hwt : t * w * t⁻¹ = y := by
    have htt : (t * t) * y = y * (t * t) := by
      rw [← pow_two]
      exact hcenO (t ^ 2) ht2 y hy
    calc t * w * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by rw [hw]; group
      _ = y * (t * t) * (t * t)⁻¹ := by rw [htt]
      _ = y := by group
  have hwk : k * w = w * k := by
    have hK : t * k * t⁻¹ = (t * k * t⁻¹ * k) * k⁻¹ := by group
    have hcj : (t * k * t⁻¹ * k) * k⁻¹ * w = w * ((t * k * t⁻¹ * k) * k⁻¹) := by
      rw [← hK]
      calc (t * k * t⁻¹) * w = t * (k * y) * t⁻¹ := by rw [hw]; group
        _ = t * (y * k) * t⁻¹ := by rw [hcomm]
        _ = w * (t * k * t⁻¹) := by rw [hw]; group
    have huw : (t * k * t⁻¹ * k) * w = w * (t * k * t⁻¹ * k) :=
      hcenQ _ (hO2Q hu) w hwY
    have h1 : (t * k * t⁻¹ * k) * (k⁻¹ * w) = (t * k * t⁻¹ * k) * (w * k⁻¹) := by
      calc (t * k * t⁻¹ * k) * (k⁻¹ * w) = (t * k * t⁻¹ * k) * k⁻¹ * w := by group
        _ = w * ((t * k * t⁻¹ * k) * k⁻¹) := hcj
        _ = (w * (t * k * t⁻¹ * k)) * k⁻¹ := by group
        _ = ((t * k * t⁻¹ * k) * w) * k⁻¹ := by rw [huw]
        _ = (t * k * t⁻¹ * k) * (w * k⁻¹) := by group
    have h2 : k⁻¹ * w = w * k⁻¹ := mul_left_cancel h1
    have h3 : w = k * w * k⁻¹ := by
      calc w = k * (k⁻¹ * w) := by group
        _ = k * (w * k⁻¹) := by rw [h2]
        _ = k * w * k⁻¹ := by group
    calc k * w = (k * w * k⁻¹) * k := by group
      _ = w * k := by rw [← h3]
  by_cases hyw : y * w = 1
  · have hyy : y * y = 1 := by
      rw [← pow_two]
      exact hY2el.2 y hy
    have hwy : w = y := by
      have h1 : w = y⁻¹ := eq_inv_of_mul_eq_one_right hyw
      rw [h1]
      exact inv_eq_of_mul_eq_one_right hyy
    have htc : t * y * t⁻¹ = y := hw.symm.trans hwy
    have hall := fix_centralizes e htL hk ht1 ht2 hk3 hcomm htc
      (fun o ho => hcenO o ho y hy)
    exact hy1 (c_L2 h cJ hy hall)
  · have hyY : y * w ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) := Subgroup.mul_mem _ hy hwY
    have hkc : k * (y * w) = (y * w) * k := by
      calc k * (y * w) = (k * y) * w := by group
        _ = (y * k) * w := by rw [hcomm]
        _ = y * (k * w) := by group
        _ = y * (w * k) := by rw [hwk]
        _ = (y * w) * k := by group
    have htc : t * (y * w) * t⁻¹ = y * w := by
      have hcomm' : w * y = y * w := F7.isElemAbelian_comm hY2el hwY hy
      calc t * (y * w) * t⁻¹ = (t * y * t⁻¹) * (t * w * t⁻¹) := by group
        _ = w * y := by rw [hwt, ← hw]
        _ = y * w := hcomm'
    have hall := fix_centralizes e htL hk ht1 ht2 hk3 hkc htc
      (fun o ho => hcenO o ho _ hyY)
    exact hyw (c_L2 h cJ hyY hall)


theorem j2 [Finite4 G] [DSLeaf LeafZiStructure] [DSLeaf LeafSylowS] [DSLeaf LeafDSBS3Vertex]
    [DSLeaf LeafS3Module] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S)
    (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    dsZi L2 S = dsOmega1 (centerOf (dsQ L2 L1 S)) ∧
      (∀ k ∈ L2, orderOf k = 3 → FixFree ⊥ (dsZi L2 S) k) ∧
      Nat.card (dsZi L2 S) = Nat.card (dsZ S) ^ 2 ∧ Nat.card (dsZ S) ≤ 4 := by
  have hyp2 : Hyp111R L2 L1 S := h.hyp.symm
  have hZS2 : ZSetting L2 L1 S := ZSetting.symm ⟨h.hyp, DSBHyp.bnorm h⟩
  have hZi : dsZi L1 S = dsZ S := dsZi_eq_dsZ_of_commutator_eq_bot cJ
  obtain ⟨-, hZZ2, hZY2, hY2el, hY2card, hP2Z, hP2Y⟩ := zi_structure hZS2
  obtain ⟨e⟩ := h.s3
  have hQ2S : dsQ L2 L1 S ≤ S := (sylow_s hyp2).2.2
  have hO2Q : pCoreOf 2 L2 ≤ dsQ L2 L1 S := F1.pCoreOf_le_pCoreOf_parabolic hyp2
  obtain ⟨hd3, -, -, -⟩ := dsbs3_vertex h
  have hY2Q : dsOmega1 (centerOf (dsQ L2 L1 S)) ≤ dsQ L2 L1 S :=
    (omega_centerOf_le _).trans (centerOf_le _)
  have hZY : dsZ S ≤ dsOmega1 (centerOf (dsQ L2 L1 S)) := hZZ2.trans hZY2
  have hconjY : ∀ g ∈ L2, ∀ y ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
      g * y * g⁻¹ ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hP2Y ((le_sup_left : L2 ≤ L2 ⊔ bigB L2 L1 S) hg)) y).mp hy
  have hcenQ : ∀ q ∈ dsQ L2 L1 S, ∀ w ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
      q * w = w * q := fun q hq w hw => (mem_centerOf_iff.mp (omega_centerOf_le _ hw)).2 q hq
  have hcen : dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓
      Subgroup.centralizer ((S ⊓ L2 : Subgroup G) : Set G) = dsZ S := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxc2 : x ∈ centerOf (dsQ L2 L1 S) := omega_centerOf_le _ hxY
      have hxS : x ∈ S := hQ2S (centerOf_le _ hxc2)
      have key := comm_sup (A := S ⊓ L2) (B := dsQ L2 L1 S) (x := x)
        (fun a ha => (Subgroup.mem_centralizer_iff.mp hxC) a ha)
        (fun b hb => (mem_centerOf_iff.mp hxc2).2 b hb)
      rw [← hd3] at key
      exact mem_omega_of (mem_centerOf_iff.mpr ⟨hxS, key⟩) (hY2el.2 x hxY)
    · intro z hz
      have hzc : z ∈ centerOf S := dsZ_le_center S hz
      refine Subgroup.mem_inf.mpr ⟨hZY hz, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact (mem_centerOf_iff.mp hzc).2 a (Subgroup.mem_inf.mp ha).1
  have hffall : ∀ k ∈ L2, orderOf k = 3 →
      FixFree ⊥ (dsOmega1 (centerOf (dsQ L2 L1 S))) k := by
    intro k hk hk3 y hy hc
    have hc' : y * k = k * y := commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hc)
    exact Subgroup.mem_bot.mpr (c_k h cJ hk hk3 hy hc'.symm)
  obtain ⟨k, hk, hk3⟩ := exists_order3 e
  have hcard_eq : Nat.card (dsOmega1 (centerOf (dsQ L2 L1 S))) = Nat.card (dsZ S) ^ 2 := by
    have hLY : L2 ≤ Subgroup.normalizer ((dsOmega1 (centerOf (dsQ L2 L1 S)) : Subgroup G) :
        Set G) := (le_sup_left : L2 ≤ L2 ⊔ bigB L2 L1 S).trans hP2Y
    have hc : ∀ q ∈ pCoreOf 2 L2, ∀ y ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
        ⁅q, y⁆ = 1 := fun q hq y hy =>
      commutatorElement_eq_one_iff_mul_comm.mpr ((mem_centerOf_iff.mp (omega_centerOf_le _ hy)).2
        q (hO2Q hq))
    have hS3 := s3_module ⟨e⟩ hY2el hLY hc hk hk3 (hffall k hk hk3) h.hyp.hyp.h2.sylow
    rw [hcen] at hS3
    exact hS3
  have hZ4 : Nat.card (dsZ S) ≤ 4 := by
    have h16 := hY2card
    rw [hcard_eq] at h16
    nlinarith
  have hZ2eq : dsZi L2 S = dsOmega1 (centerOf (dsQ L2 L1 S)) := by
    apply Subgroup.eq_of_le_of_card_ge hZY2
    have hk3' : k ^ 3 = 1 := by
      rw [← hk3]
      exact pow_orderOf_eq_one k
    have hkkk : k * k * k = 1 := by
      rw [← pow_three']
      exact hk3'
    have hk2 : k⁻¹ * k⁻¹ = k := by
      calc k⁻¹ * k⁻¹ = k⁻¹ * k⁻¹ * (k * k * k) := by rw [hkkk, mul_one]
        _ = k := by group
    have hk2' : k * k = k⁻¹ := eq_inv_of_mul_eq_one_left hkkk
    set Zc : Subgroup G := (dsZ S).map (MulAut.conj k).toMonoidHom with hZc
    have hZcle : Zc ≤ dsZi L2 S := by
      rintro _ ⟨z, hz, rfl⟩
      exact conj_mem_dsConjClosure hk hz
    have hZcard : Nat.card Zc = Nat.card (dsZ S) :=
      Subgroup.card_map_of_injective (MulAut.conj k).injective
    have hZZc : dsZ S ⊓ Zc = ⊥ := by
      rw [eq_bot_iff]
      rintro z hz
      obtain ⟨hzZ, hzZc⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨z', hz'Z, hz'⟩ := Subgroup.mem_map.mp hzZc
      have hzeq : z = k * z' * k⁻¹ := hz'.symm
      have hz'eq : z' = k⁻¹ * z * k := by
        rw [hzeq]
        group
      have hzY : z ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) := hZY hzZ
      have hz'Y : z' ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) := hZY hz'Z
      obtain ⟨t, htS, htQ, ht2⟩ := exists_t h
      have htL : t ∈ L2 := (Subgroup.mem_inf.mp htS).2
      have htS' : t ∈ S := (Subgroup.mem_inf.mp htS).1
      have ht1 : t ∉ pCoreOf 2 L2 := fun h1 => htQ (hO2Q h1)
      have ht_comm : ∀ w ∈ dsZ S, t * w * t⁻¹ = w := fun w hw => by
        have htw := (mem_centerOf_iff.mp (dsZ_le_center S hw)).2 t htS'
        rw [htw]
        group
      have hu := s3_rel e htL hk ht1 ht2 hk3
      have hu_Q : t * k * t⁻¹ * k ∈ dsQ L2 L1 S := hO2Q hu
      have hR2 : ∀ y ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
          (t * k * t⁻¹) * y * (t * k * t⁻¹)⁻¹ = k⁻¹ * y * k := by
        intro y hy
        have hyk : k⁻¹ * y * k ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) := by
          have := hconjY k⁻¹ (L2.inv_mem hk) y hy
          rwa [inv_inv] at this
        have hcu := hcenQ _ hu_Q _ hyk
        calc (t * k * t⁻¹) * y * (t * k * t⁻¹)⁻¹
            = (t * k * t⁻¹ * k) * (k⁻¹ * y * k) * (t * k * t⁻¹ * k)⁻¹ := by group
          _ = ((k⁻¹ * y * k) * (t * k * t⁻¹ * k)) * (t * k * t⁻¹ * k)⁻¹ := by rw [hcu]
          _ = k⁻¹ * y * k := by group
      have hz1 : z = k⁻¹ * z' * k := by
        calc z = t * z * t⁻¹ := (ht_comm z hzZ).symm
          _ = t * (k * z' * k⁻¹) * t⁻¹ := by rw [hzeq]
          _ = (t * k * t⁻¹) * (t * z' * t⁻¹) * (t * k * t⁻¹)⁻¹ := by group
          _ = (t * k * t⁻¹) * z' * (t * k * t⁻¹)⁻¹ := by rw [ht_comm z' hz'Z]
          _ = k⁻¹ * z' * k := hR2 z' hz'Y
      have hzk : k * z = z * k := by
        have h1 : z = k * z * k⁻¹ := by
          calc z = k⁻¹ * z' * k := hz1
            _ = k⁻¹ * (k⁻¹ * z * k) * k := by rw [hz'eq]
            _ = (k⁻¹ * k⁻¹) * z * (k * k) := by group
            _ = k * z * k⁻¹ := by rw [hk2, hk2']
        calc k * z = (k * z * k⁻¹) * k := by group
          _ = z * k := by rw [← h1]
      exact Subgroup.mem_bot.mpr (c_k h cJ hk hk3 hzY hzk)
    let f : ↥(dsZ S) × ↥Zc → ↥(dsZi L2 S) := fun p =>
      ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem _ (dsZ_le_dsZi L2 S p.1.2) (hZcle p.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have hab' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
      have hmul : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [hab']
          _ = (b' : G) * (b : G)⁻¹ := by group
      have h1 : (a' : G)⁻¹ * (a : G) ∈ dsZ S ⊓ Zc := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a'.2) a.2, ?_⟩
        rw [hmul]
        exact Subgroup.mul_mem _ b'.2 (Subgroup.inv_mem _ b.2)
      rw [hZZc, Subgroup.mem_bot] at h1
      have hb1 : (b' : G) * (b : G)⁻¹ = 1 := by
        rw [← hmul]
        exact h1
      have hab2 : a = a' := Subtype.ext (inv_mul_eq_one.mp h1).symm
      have hbb2 : b = b' := Subtype.ext (mul_inv_eq_one.mp hb1).symm
      rw [hab2, hbb2]
    have hle : Nat.card (↥(dsZ S) × ↥Zc) ≤ Nat.card ↥(dsZi L2 S) :=
      Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hZcard] at hle
    rw [hcard_eq, sq]
    exact hle
  refine ⟨hZ2eq, fun k' hk' hk'3 => ?_, ?_, hZ4⟩
  · rw [hZ2eq]
    exact hffall k' hk' hk'3
  · rw [hZ2eq, hcard_eq]

theorem j2d [Finite4 G] [DSLeaf LeafZiStructure] [DSLeaf LeafDSBS3Vertex] {L1 L2 S : Subgroup G}
    (h : DSBHyp L1 L2 S) (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    ∀ d ∈ borelOf L1 S, orderOf d = 3 → ∀ z ∈ dsZi L2 S, ⁅d, z⁆ = 1 := by
  intro d hd hd3
  have hdL1 : d ∈ L1 := (Subgroup.mem_inf.mp hd).1
  have hZS2 : ZSetting L2 L1 S := ZSetting.symm ⟨h.hyp, DSBHyp.bnorm h⟩
  have hZi : dsZi L1 S = dsZ S := dsZi_eq_dsZ_of_commutator_eq_bot cJ
  obtain ⟨-, hZZ2, hZY2, -, -, -, -⟩ := zi_structure hZS2
  obtain ⟨-, -, hdconj, -⟩ := dsbs3_vertex h
  have hZY : dsZ S ≤ dsOmega1 (centerOf (dsQ L2 L1 S)) := hZZ2.trans hZY2
  have hd3' : orderOf d⁻¹ = 3 := by
    rw [orderOf_inv]
    exact hd3
  have hK : dsConjClosure L2 (dsZ S) ≤ Subgroup.centralizer ({d} : Set G) := by
    refine dsConjClosure_le' fun y hy z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    have hzY : z ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) := hZY hz
    have hzZ1 : z ∈ dsZi L1 S := by
      rw [hZi]
      exact hz
    have hdz : d * z = z * d := comm_of_cJ cJ hzZ1 d hdL1
    have hq : d⁻¹ * y⁻¹ * d * y ∈ dsQ L2 L1 S := by
      have := hdconj d⁻¹ ((borelOf L1 S).inv_mem hd) hd3' y⁻¹ (L2.inv_mem hy)
      rw [commutatorElement_def, inv_inv, inv_inv] at this
      exact this
    have hqz : (d⁻¹ * y⁻¹ * d * y) * z = z * (d⁻¹ * y⁻¹ * d * y) :=
      (mem_centerOf_iff.mp (omega_centerOf_le _ hzY)).2 _ hq
    have hc1 : (y⁻¹ * d * y) * z = z * (y⁻¹ * d * y) := by
      calc (y⁻¹ * d * y) * z = d * ((d⁻¹ * y⁻¹ * d * y) * z) := by group
        _ = d * (z * (d⁻¹ * y⁻¹ * d * y)) := by rw [hqz]
        _ = (d * z) * (d⁻¹ * y⁻¹ * d * y) := by group
        _ = (z * d) * (d⁻¹ * y⁻¹ * d * y) := by rw [hdz]
        _ = z * (y⁻¹ * d * y) := by group
    calc d * (y * z * y⁻¹) = y * ((y⁻¹ * d * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * d * y)) * y⁻¹ := by rw [hc1]
      _ = (y * z * y⁻¹) * d := by group
  intro z hz
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp (hK hz) d
    (Set.mem_singleton d))


theorem j3 [Finite4 G] [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafSylowS] [DSLeaf LeafDSBS3Vertex]
    [DSLeaf LeafZiStructure] [DSLeaf LeafM5] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S)
    (cJ : ⁅dsZi L1 S, L1⁆ = ⊥)
    (hdcen : ∀ d ∈ borelOf L1 S, orderOf d = 3 → ∀ z ∈ dsZi L2 S, ⁅d, z⁆ = 1) :
    dsZi L2 S ≤ dsQ L1 L2 S := by
  have hyp : Hyp111R L1 L2 S := h.hyp
  have hyp2 : Hyp111R L2 L1 S := h.hyp.symm
  have hZS2 : ZSetting L2 L1 S := ZSetting.symm ⟨h.hyp, DSBHyp.bnorm h⟩
  obtain ⟨-, -, hZY2, -, -, hP2Z, -⟩ := zi_structure hZS2
  have hQ2S : dsQ L2 L1 S ≤ S := (sylow_s hyp2).2.2
  have hY2Q : dsOmega1 (centerOf (dsQ L2 L1 S)) ≤ dsQ L2 L1 S :=
    (omega_centerOf_le _).trans (centerOf_le _)
  have hZ2S : dsZi L2 S ≤ S := (hZY2.trans hY2Q).trans hQ2S
  have hA5 : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 hyp h.ns1
  have hT : IsSylowTwoOf (S ⊓ L1) L1 := h.hyp.hyp.h1.sylow
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) := hA5.quot
  obtain ⟨hM5a, hM5b⟩ := m5 hq1 hT
  obtain ⟨hd5S, hd5rel, hd5Q⟩ := dsba5_vertex h
  have hQS1 : dsQ L1 L2 S ≤ S := (sylow_s hyp).2.2
  have hpc1 : pCoreOf 2 L1 = dsQ L1 L2 S := by
    rw [← F1.inf_pCoreOf_parabolic_eq hyp]
    exact inf_eq_left.mpr hd5Q
  have hSP1 : S ≤ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSQ : S ⊓ L1 ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    (inf_le_right : S ⊓ L1 ≤ L1).trans
      ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hZQ : dsZi L2 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    (hZ2S.trans hSP1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hB1 : borelOf L1 S ≤ L1 := inf_le_left
  have hB1P2 : borelOf L1 S ≤ L2 ⊔ bigB L2 L1 S := by
    rw [bigB_comm]
    exact (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S).trans le_sup_right
  have hB1N2 : borelOf L1 S ≤ Subgroup.normalizer (dsZi L2 S : Set G) := hB1P2.trans hP2Z
  have hB1NQ : borelOf L1 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    (hB1.trans le_sup_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hXN : borelOf L1 S ≤
      Subgroup.normalizer (((S ⊓ L1) ⊓ (dsZi L2 S ⊔ dsQ L1 L2 S) : Subgroup G) : Set G) :=
    F7.le_normalizer_inf inf_le_right (F1.le_normalizer_sup hB1N2 hB1NQ)
  have hpcS : pCoreOf 2 L1 ≤ (S ⊓ L1) ⊓ (dsZi L2 S ⊔ dsQ L1 L2 S) := by
    rw [hpc1]
    exact le_inf (le_inf hQS1 hd5Q) le_sup_right
  rcases hM5a _ hpcS inf_le_left hXN with hXQ | hXT
  ·
    rw [hpc1] at hXQ
    intro z hz
    have hzS : z ∈ S := hZ2S hz
    have hdec : z ∈ (S ⊓ L1) ⊔ dsQ L1 L2 S := by
      rw [← hd5S]
      exact hzS
    obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hSQ).mp hdec
    have haX : a ∈ dsZi L2 S ⊔ dsQ L1 L2 S := by
      have hae : a = z * b⁻¹ := by
        rw [hab]
        group
      rw [hae]
      exact Subgroup.mul_mem _ ((le_sup_left : dsZi L2 S ≤ dsZi L2 S ⊔ dsQ L1 L2 S) hz)
        ((le_sup_right : dsQ L1 L2 S ≤ dsZi L2 S ⊔ dsQ L1 L2 S) (Subgroup.inv_mem _ hb))
    have haQ : a ∈ dsQ L1 L2 S := by
      rw [← hXQ]
      exact Subgroup.mem_inf.mpr ⟨ha, haX⟩
    rw [hab]
    exact Subgroup.mul_mem _ haQ hb
  ·
    exfalso
    have hST : S ⊓ L1 ≤ dsZi L2 S ⊔ dsQ L1 L2 S := by
      intro x hx
      have hx' : x ∈ (S ⊓ L1) ⊓ (dsZi L2 S ⊔ dsQ L1 L2 S) := by
        rw [hXT]
        exact hx
      exact (Subgroup.mem_inf.mp hx').2
    have hSle : S ≤ dsZi L2 S ⊔ dsQ L1 L2 S := by
      intro x hx
      have hx' : x ∈ (S ⊓ L1) ⊔ dsQ L1 L2 S := by
        rw [← hd5S]
        exact hx
      obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hSQ).mp hx'
      rw [hab]
      exact Subgroup.mul_mem _ (hST ha) ((le_sup_right : dsQ L1 L2 S ≤ dsZi L2 S ⊔ dsQ L1 L2 S) hb)
    obtain ⟨⟨d, hdB, hd3⟩, -⟩ := DSBA5.three_and_card hT hq1
    have hdL1 : d ∈ L1 := (Subgroup.mem_inf.mp hdB).1
    have hdN : d ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
        ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hdL1)
    have hcommS : ∀ s ∈ S, ⁅s, d⁆ ∈ dsQ L1 L2 S := by
      intro s hs
      obtain ⟨z, hz, q, hq, hsq⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hZQ).mp (hSle hs)
      have hdz1 : d * z = z * d := commutatorElement_eq_one_iff_mul_comm.mp (hdcen d hdB hd3 z hz)
      have hdzd : d * z * d⁻¹ = z := by
        rw [hdz1]
        group
      have hdzi : d * z⁻¹ * d⁻¹ = z⁻¹ := by
        calc d * z⁻¹ * d⁻¹ = (d * z * d⁻¹)⁻¹ := by group
          _ = z⁻¹ := by rw [hdzd]
      have hdq' : d * q⁻¹ * d⁻¹ ∈ dsQ L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp hdN q⁻¹).mp (Subgroup.inv_mem _ hq)
      have hc : q * d * q⁻¹ * d⁻¹ ∈ dsQ L1 L2 S := by
        have e1 : q * d * q⁻¹ * d⁻¹ = q * (d * q⁻¹ * d⁻¹) := by group
        rw [e1]
        exact Subgroup.mul_mem _ hq hdq'
      have hcomm_eq : ⁅s, d⁆ = z * (q * d * q⁻¹ * d⁻¹) * z⁻¹ := by
        rw [commutatorElement_def, hsq]
        calc z * q * d * (z * q)⁻¹ * d⁻¹
            = z * (q * d * q⁻¹ * d⁻¹) * (d * z⁻¹ * d⁻¹) := by group
          _ = z * (q * d * q⁻¹ * d⁻¹) * z⁻¹ := by rw [hdzi]
      rw [hcomm_eq]
      exact (Subgroup.mem_normalizer_iff.mp (hZQ hz) _).mp hc
    have hex : ∃ e ∈ S ⊓ L1, e ∉ dsQ L1 L2 S := by
      by_contra hcon
      have hSQ' : S ≤ dsQ L1 L2 S := by
        intro x hx
        have hx' : x ∈ (S ⊓ L1) ⊔ dsQ L1 L2 S := by
          rw [← hd5S]
          exact hx
        obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hSQ).mp hx'
        have ha' : a ∈ dsQ L1 L2 S := by
          by_contra hac
          exact hcon ⟨a, ha, hac⟩
        rw [hab]
        exact Subgroup.mul_mem _ ha' hb
      have heq : S = dsQ L1 L2 S := le_antisymm hSQ' hQS1
      have hrel1 : (dsQ L1 L2 S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr heq.le
      rw [hrel1] at hd5rel
      norm_num at hd5rel
    obtain ⟨e, he, heQ⟩ := hex
    have hff := hM5b d hdB hd3
    have hcE : ⁅e, d⁆ ∈ pCoreOf 2 L1 := by
      rw [hpc1]
      exact hcommS e (Subgroup.mem_inf.mp he).1
    exact heQ (hpc1 ▸ hff e he hcE)

end DSBJZ2

theorem leafDSBJZ2 [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafDSBS3Vertex] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafFrattiniChief] [DSLeaf LeafFaithfulA5] [DSLeaf LeafM5] [DSLeaf LeafS3Module] [DSLeaf LeafM7] [DSLeaf LeafSylowS] [DSLeaf LeafRankBounds] : LeafDSBJZ2 := by
  intro G _ _ L1 L2 S h cJ
  obtain ⟨hJ2a, hJ2b, hJ2c, hJ2d⟩ := DSBJZ2.j2 h cJ
  have hJ2e := DSBJZ2.j2d h cJ
  exact ⟨DSBJZ2.j1 h cJ, ⟨hJ2a, hJ2b, hJ2c, hJ2d, hJ2e⟩, DSBJZ2.j3 h cJ hJ2e⟩

end CFSG.GH74.QTGen4.DSGen4
