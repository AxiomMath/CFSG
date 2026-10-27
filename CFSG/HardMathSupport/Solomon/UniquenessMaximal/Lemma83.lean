module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Vocab
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
import CFSG.Adapters.GeneralizedFitting
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof
import CFSG.LocalAnalysis.GLTheoremB.LayerTools
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section FStar

variable {Q : Type*} [Group Q]

theorem genFittingFStar_conj_mem {g x : Q} (hx : x ∈ genFittingFStar Q) :
    g * x * g⁻¹ ∈ genFittingFStar Q := by
  let H : Subgroup Q := (genFittingFStar Q).comap (MulAut.conj g).toMonoidHom
  have hF : genFittingFitting Q ≤ H := by
    have : (genFittingFitting Q).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
    intro y hy
    exact (le_sup_left : genFittingFitting Q ≤ genFittingFStar Q) (this.conj_mem y hy g)
  have hE : genFittingLayer Q ≤ H := by
    refine sSup_le fun K hK => ?_
    intro k hk
    have hK' := isComponentOf_gLBConj hK g⁻¹
    have : g * k * g⁻¹ ∈ GLBConj g⁻¹ K := by
      rw [mem_gLBConj]
      have e : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
      rw [e]; exact hk
    have hmem : GLBConj g⁻¹ K ≤ genFittingLayer Q :=
      le_sSup (show GLBConj g⁻¹ K ∈ {L | IsComponentOf L ⊤} from hK')
    exact (le_sup_right : genFittingLayer Q ≤ genFittingFStar Q) (hmem this)
  exact (sup_le hF hE : genFittingFStar Q ≤ H) hx

omit [Group Q] in
theorem aut_apply_eq_of_fstar {Q : Type} [Group Q] [Finite Q] (α : MulAut Q) (n : ℕ)
    (hn : ∀ q, (α ^ n) q = q) (hcop : Nat.Coprime n (Nat.card Q))
    (hfix : ∀ f ∈ genFittingFStar Q, α f = f) (x : Q) : α x = x := by
  set φ : Q := x⁻¹ * α x with hφdef
  have hφ : φ ∈ Subgroup.centralizer (genFittingFStar Q : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h2 := hfix _ (genFittingFStar_conj_mem (g := x) hf)
    rw [map_mul, map_mul, hfix f hf, map_inv] at h2
    have h3 : α x * f = x * f * x⁻¹ * α x := by
      rw [← h2]; group
    calc f * φ = f * (x⁻¹ * α x) := rfl
      _ = x⁻¹ * (x * f * x⁻¹ * α x) := by group
      _ = x⁻¹ * (α x * f) := by rw [h3]
      _ = φ * f := by rw [hφdef]; group
  have hφF : φ ∈ genFittingFStar Q := CFSG.Adapters.generalized_fitting_self_centralizing Q hφ
  have hαφ : α φ = φ := hfix φ hφF
  have hpow : ∀ k : ℕ, (α ^ k) x = x * φ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαφ, pow_succ']
      have : α x = x * φ := by rw [hφdef]; group
      rw [this]; group
  have h1 : φ ^ n = 1 := by
    have := hpow n
    rw [hn x] at this
    exact (mul_eq_left.1 this.symm)
  have h2 : orderOf φ ∣ Nat.gcd n (Nat.card Q) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard φ)
  rw [hcop] at h2
  have : φ = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)
  have : α x = x * φ := by rw [hφdef]; group
  rw [this, ‹φ = 1›, mul_one]

end FStar

section Quot

variable {G : Type} [Group G] [Finite G]

theorem fstar_le_barX_layerPreimage (X : Subgroup G) :
    genFittingFStar (↥X ⧸ GLAPPrimeCore 2 ↥X) ≤ barX 2 X (layerPreimage X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : CFSG.pPrimeCore 2 (↥X ⧸ GLAPPrimeCore 2 ↥X) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot Nat.prime_two
  refine sup_le ?_ ?_
  · have hF : CFSG.fittingSubgroup (↥X ⧸ GLAPPrimeCore 2 ↥X) =
        CFSG.pCore 2 (↥X ⧸ GLAPPrimeCore 2 ↥X) := CFSG.Fitting_eq_pcore _ 2 hbot
    show CFSG.fittingSubgroup (↥X ⧸ GLAPPrimeCore 2 ↥X) ≤ _
    rw [hF]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨x, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (le_sup_right (a := GLAPLayer 2 X)
      (show (x : G) ∈ oTwoPrimeTwo X from ⟨x, hq, rfl⟩))
  · refine sSup_le fun K hK => ?_
    obtain ⟨L, hL, hbar⟩ := exists_glaPComponent_barX_eq (p := 2) X hK
    rw [← hbar]
    have hLle : L ≤ layerPreimage X := (le_sSup hL : L ≤ GLAPLayer 2 X).trans le_sup_left
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, Subgroup.mem_subgroupOf.2 (hLle (Subgroup.mem_subgroupOf.1 hz)), rfl⟩

theorem commutator_mem_oTwo {X : Subgroup G} {b : G} (hbX : b ∈ Subgroup.normalizer (X : Set G))
    {n : ℕ} (hbn : b ^ n = 1) (hcop : Nat.Coprime n (Nat.card X))
    (hcent : ∀ y ∈ layerPreimage X, b * y * b⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 2 X) :
    ∀ x ∈ X, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 2 X := by
  set K := GLAPPrimeCore 2 ↥X with hK
  let φ : MulAut X := X.normalizerMonoidHom ⟨b, hbX⟩
  have hφc : ∀ y : X, ((φ y : X) : G) = b * y * b⁻¹ := fun y =>
    X.normalizerMonoidHom_apply_apply_coe ⟨b, hbX⟩ y
  have hφpow : ∀ (k : ℕ) (y : X), (((φ ^ k) y : X) : G) = b ^ k * y * (b ^ k)⁻¹ := by
    intro k y
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, hφc, ih, pow_succ]
      group
  let α : MulAut (↥X ⧸ K) := QuotientGroup.congr K K φ (glaPPrimeCore_map_iso 2 φ)
  have hαmk : ∀ (k : ℕ) (y : X), (α ^ k) (y : ↥X ⧸ K) = ((φ ^ k) y : X) := by
    intro k y
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' α k, MulAut.mul_apply, ih, pow_succ' φ k, MulAut.mul_apply]
      exact QuotientGroup.congr_mk K K φ (glaPPrimeCore_map_iso 2 φ) _
  have hn : ∀ q, (α ^ n) q = q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hαmk]
    congr 1
    apply Subtype.ext
    rw [hφpow, hbn]
    simp
  have hcop' : Nat.Coprime n (Nat.card (↥X ⧸ K)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card K) hcop
  have hmemK : ∀ y : X, (b * y * b⁻¹ * (y : G)⁻¹) ∈ GLAPPrimeCoreOf 2 X → φ y / y ∈ K := by
    intro y h
    have : X.subtype (φ y / y) ∈ K.map X.subtype := by
      have e : X.subtype (φ y / y) = b * y * b⁻¹ * (y : G)⁻¹ := by
        simp [hφc, div_eq_mul_inv]
      rw [e]; exact h
    exact (Subgroup.mem_map_iff_mem X.subtype_injective).1 this
  have hfix : ∀ f ∈ genFittingFStar (↥X ⧸ K), α f = f := by
    intro f hf
    obtain ⟨y, hy, rfl⟩ := fstar_le_barX_layerPreimage X hf
    have hy' := Subgroup.mem_subgroupOf.1 hy
    have h1 : (α ^ 1) (y : ↥X ⧸ K) = ((φ ^ 1) y : X) := hαmk 1 y
    rw [pow_one, pow_one] at h1
    show α (y : ↥X ⧸ K) = y
    rw [h1]
    exact (QuotientGroup.eq_iff_div_mem).2 (hmemK y (hcent y hy'))
  intro x hx
  have h := aut_apply_eq_of_fstar α n hn hcop' hfix ((⟨x, hx⟩ : X) : ↥X ⧸ K)
  have h1 : α ((⟨x, hx⟩ : X) : ↥X ⧸ K) = ((φ ⟨x, hx⟩ : X) : ↥X ⧸ K) := by
    have := hαmk 1 ⟨x, hx⟩
    rwa [pow_one, pow_one] at this
  rw [h1] at h
  have hm := (QuotientGroup.eq_iff_div_mem).1 h
  refine ⟨_, hm, ?_⟩
  simp [hφc, div_eq_mul_inv]

theorem exists_mul_mem_normalizer_of_sylow {q : ℕ} [Fact q.Prime] {X S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hSX : S ≤ X) (hS : IsPGroup q S)
    (hmax : ∀ n : ℕ, q ^ n ∣ Nat.card X → q ^ n ∣ Nat.card S) :
    ∃ x ∈ X, x * g ∈ Subgroup.normalizer (S : Set G) := by
  have hq : q.Prime := Fact.out
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hXpos : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hkle : k ≤ (Nat.card X).factorization q :=
    (hq.pow_dvd_iff_le_factorization hXpos).1 (hk ▸ Subgroup.card_dvd_of_le hSX)
  have hekle : (Nat.card X).factorization q ≤ k := by
    have := hk ▸ hmax _ (Nat.ordProj_dvd (Nat.card X) q)
    exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).1 this
  have hcardS : Nat.card (S.subgroupOf X) = q ^ (Nat.card X).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hk]
    congr 1
    omega
  let S' : Subgroup G := S.map (MulAut.conj g).toMonoidHom
  have hS'X : S' ≤ X := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg s).1 (hSX hs) |> fun h => by simpa using h
  have hcardS' : Nat.card (S'.subgroupOf X) = q ^ (Nat.card X).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'X).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hk]
    congr 1
    omega
  let P : Sylow q X := Sylow.ofCard (S.subgroupOf X) hcardS
  let P' : Sylow q X := Sylow.ofCard (S'.subgroupOf X) hcardS'
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P P'
  refine ⟨(x⁻¹ : X), (x⁻¹ : X).2, ?_⟩
  refine Subgroup.mem_normalizer_fintype fun h hh => ?_
  have hz : (⟨g * h * g⁻¹, hS'X ⟨h, hh, by simp⟩⟩ : X) ∈ (P' : Subgroup X) :=
    Subgroup.mem_subgroupOf.2 ⟨h, hh, by simp⟩
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
  have := Subgroup.mem_subgroupOf.1 hz
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem le_glaPPrimeCoreOf_of_frattini {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M₀ N R : Subgroup G}
    (hRM : R ≤ M₀) (hR : IsPGroup 2 R) (hRN : N ≤ Subgroup.normalizer (R : Set G))
    (hfr : ∀ g ∈ M₀, ∃ x ∈ GLAPPrimeCoreOf p M₀, x * g ∈ N) : R ≤ GLAPPrimeCoreOf p M₀ := by
  set X := GLAPPrimeCoreOf p M₀ with hXdef
  have hXM : X ≤ M₀ := Subgroup.map_subtype_le _
  have hnormX : M₀ ≤ Subgroup.normalizer (X : Set G) := fun m hm => by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    exact mem_gLAPPrimeCoreOf_conj hx hm
  set Xs : Subgroup M₀ := X.subgroupOf M₀ with hXs
  have hXsN : Xs.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hnormX
  set R₀ : Subgroup M₀ := R.subgroupOf M₀ with hR₀
  set Rbar : Subgroup (↥M₀ ⧸ Xs) := R₀.map (QuotientGroup.mk' Xs) with hRbar
  have hRbarN : Rbar.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨r0, hr0, rfl⟩ := ha
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨x, hx, hxg⟩ := hfr g0.1 g0.2
    have hxM : x ∈ M₀ := hXM hx
    set n0 : M₀ := ⟨x * g0, M₀.mul_mem hxM g0.2⟩ with hn0
    have hmk : (QuotientGroup.mk' Xs) n0 = (g0 : ↥M₀ ⧸ Xs) := by
      have : n0 = ⟨x, hxM⟩ * g0 := rfl
      rw [QuotientGroup.mk'_apply, this, QuotientGroup.mk_mul]
      have h1 : ((⟨x, hxM⟩ : M₀) : ↥M₀ ⧸ Xs) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)
      rw [h1, one_mul]
    refine ⟨n0 * r0 * n0⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ?_
      have hr : (r0 : G) ∈ R := Subgroup.mem_subgroupOf.1 hr0
      have := (Subgroup.mem_normalizer_iff.1 (hRN hxg) (r0 : G)).1 hr
      simpa [hn0] using this
    · rw [map_mul, map_mul, map_inv, hmk]
  have hRbarp : IsPGroup 2 Rbar := by
    have : IsPGroup 2 R₀ := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm
    exact this.map _
  obtain ⟨j, hj⟩ := hRbarp.exists_card_eq
  set Wsub : Subgroup M₀ := Rbar.comap (QuotientGroup.mk' Xs) with hW
  have hWn : Wsub.Normal := hRbarN.comap _
  have hWcard : Nat.card Wsub = Nat.card Xs * Nat.card Rbar :=
    QuotientGroup.card_preimage_mk Xs (Rbar : Set (↥M₀ ⧸ Xs))
  have hcop : Nat.Coprime p (Nat.card Wsub) := by
    rw [hWcard]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp M₀)
    · rw [hj]
      refine Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp2 ?_)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
  have hle : Wsub ≤ GLAPPrimeCore p ↥M₀ := le_sSup ⟨hWn, hcop⟩
  intro r hr
  have : (⟨r, hRM hr⟩ : M₀) ∈ Wsub :=
    ⟨⟨r, hRM hr⟩, Subgroup.mem_subgroupOf.2 hr, rfl⟩
  exact ⟨_, hle this, rfl⟩

end Quot


variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem lemma83 (hS : GLStanding G m p) {B M₀ : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsPreUniquenessSubgroup p B M₀) {b : G} (hb : b ∈ B)
    (hcent : ∀ y ∈ layerPreimage (GLAPPrimeCoreOf p M₀),
      b * y * b⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀)) :
    b = 1 := by
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := GLAPPrimeCoreOf p M₀ with hXdef
  have hnormX : M₀ ≤ Subgroup.normalizer (X : Set G) := fun m hm => by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    exact mem_gLAPPrimeCoreOf_conj hx hm
  have hBM : B ≤ M₀ := hM.le hS hB
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := hBM.trans hnormX
  have hbp : b ^ p = 1 := hB.1.1.2 b hb
  have hXcop : ¬ p ∣ Nat.card X := not_dvd_card_glaPPrimeCoreOf hp M₀
  have hcomm := commutator_mem_oTwo (hBX hb) hbp ((Nat.Prime.coprime_iff_not_dvd hp).2 hXcop) hcent
  have hBpg : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.1.1.2 g g.2)⟩
  obtain ⟨S, hSX, hS2, hSmax, hBS⟩ :=
    exists_sylow_normalized_of_not_dvd (p := p) (q := 2) X B hBpg hBX hXcop
  have hS1 : S ≠ ⊥ := by
    intro h
    have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.1 hM.2.2
    have := hSmax 1 (by simpa using h2)
    rw [h, Subgroup.card_bot] at this
    simp at this
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hdisj : Disjoint S (GLAPPrimeCoreOf 2 X) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_two X))
  have hbS : ∀ s ∈ S, s * b = b * s := by
    intro s hs
    have h1 : b * s * b⁻¹ * s⁻¹ ∈ GLAPPrimeCoreOf 2 X := hcomm s (hSX hs)
    have h2 : b * s * b⁻¹ * s⁻¹ ∈ S :=
      S.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBS hb) s).1 hs) (S.inv_mem hs)
    have h3 := hdisj.le_bot ⟨h2, h1⟩
    rw [Subgroup.mem_bot] at h3
    have h4 : b * s = s * b := by
      calc b * s = b * s * b⁻¹ * s⁻¹ * (s * b) := by group
        _ = s * b := by rw [h3, one_mul]
    exact h4.symm
  set N := Subgroup.normalizer (S : Set G) with hN
  have hloc : IsTwoLocal N := ⟨S, hS1, hS2, rfl⟩
  have hRM : pCoreOf 2 N ≤ M₀ := hM.pCoreOf_two_le hS hB hBS
  have hRp : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hRX : pCoreOf 2 N ≤ X :=
    le_glaPPrimeCoreOf_of_frattini hp hp2 hRM hRp (le_normalizer_pCoreOf 2 N) fun g hg =>
      exists_mul_mem_normalizer_of_sylow (hnormX hg) hSX hS2 hSmax
  have hSR : S ≤ pCoreOf 2 N := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 S hS2
  have hSReq : S = pCoreOf 2 N := by
    refine Subgroup.eq_of_le_of_card_ge hSR ?_
    obtain ⟨j, hj⟩ := hRp.exists_card_eq
    have h1 : 2 ^ j ∣ Nat.card X := hj ▸ Subgroup.card_dvd_of_le hRX
    have h2 := hSmax j h1
    rw [hj]
    exact Nat.le_of_dvd Nat.card_pos h2
  have hbR : b ∈ pCoreOf 2 N := by
    have hbc : b ∈ Subgroup.centralizer (pCoreOf 2 N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hbS h (hSReq ▸ hh)
    exact hS.charTwo N hloc (Subgroup.mem_inf.2 ⟨hBS hb, hbc⟩)
  have hbX' : b ∈ X := hRX hbR
  have hord : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hbp
  rcases (Nat.dvd_prime hp).1 hord with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ Subgroup.orderOf_dvd_natCard X hbX') hXcop

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
