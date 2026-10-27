module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36HomogBound
import CFSG.Quasithin.Background.F918V3SLA
import CFSG.Quasithin.Background.F918V3SLB
import CFSG.Quasithin.Background.GoldschmidtB69DeepSec
import CFSG.Quasithin.MS93.ML3Aut
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open scoped Matrix

private theorem one_le_of_binaryNaturalSL {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} {a : ℕ} (h : BinaryNaturalSL L I Z 3 a) : 1 ≤ a := by
  obtain ⟨K, hKf, hKfin, hK, -⟩ := h
  let := hKf
  let := hKfin
  let : Fintype K := Fintype.ofFinite K
  have h2 : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rw [hK] at h2
  by_contra ha
  have h0 : a = 0 := by omega
  rw [h0, pow_zero] at h2
  omega

private theorem isGomiNatural_of_binaryNaturalSL {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} {a : ℕ} (h : BinaryNaturalSL L I Z 3 a) :
    IsGomiNatural L I Z :=
  Or.inl ⟨a, one_le_of_binaryNaturalSL h, h⟩

private theorem exists_secProj {V : Type} [CommGroup V] {K : Type} [Field K]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL 3 K) →* ↥H}
    (h : (FFModel.nat (StatedSL 3 K)).RealizesVia H U Z π) :
    ∃ f' : ↥U →* Multiplicative (Fin 3 → K), Function.Surjective f' ∧
      (∀ u : ↥U, f' u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (g : ↥(StatedSL 3 K)) (u : ↥U)
        (hu : ((π g : ↥H) : MulAut V) (u : V) ∈ U),
        f' ⟨((π g : ↥H) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd (B5.slAct g (Multiplicative.toAdd (f' u))) := by
  classical
  obtain ⟨f, hfs, hfk, hfe⟩ :=
    G64.RealizesVia.exists_secMap (D := FFModel.nat (StatedSL 3 K)) rfl h
  let f' : ↥U →* Multiplicative (Fin 3 → K) :=
    { toFun := fun u => Subtype.val (f u)
      map_one' := congrArg Subtype.val (map_one f)
      map_mul' := fun a b => congrArg Subtype.val (map_mul f a b) }
  have hf's : Function.Surjective f' := by
    intro y
    obtain ⟨x, hx⟩ := hfs (Subgroup.topEquiv.symm y)
    refine ⟨x, ?_⟩
    show Subtype.val (f x) = y
    rw [hx]
    exact Subgroup.topEquiv_symm_apply_coe y
  have hf'k : ∀ u : ↥U, f' u = 1 ↔ (u : V) ∈ Z := by
    intro u
    have h1 : f' u = 1 ↔ f u = 1 := by
      constructor
      · intro hh
        apply Subgroup.topEquiv.injective
        show Subtype.val (f u) = 1
        exact hh
      · intro hh
        show Subtype.val (f u) = 1
        rw [hh]
        rfl
    exact h1.trans (hfk u)
  have hfe' : ∀ (g : ↥(StatedSL 3 K)) (u : ↥U)
      (hu : ((π g : ↥H) : MulAut V) (u : V) ∈ U),
      f' ⟨((π g : ↥H) : MulAut V) (u : V), hu⟩ =
        Multiplicative.ofAdd (B5.slAct g (Multiplicative.toAdd (f' u))) := by
    intro g u hu
    have h1 := hfe g u hu
    change Subtype.val (f ⟨_, hu⟩) =
      Multiplicative.ofAdd (B5.slAct g (Multiplicative.toAdd (Subtype.val (f u))))
    exact h1
  exact ⟨f', hf's, hf'k, hfe'⟩

private theorem exists_coord_sec {V : Type} [CommGroup V] {K : Type} [Field K]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL 3 K) →* ↥H}
    (hHU : H ≤ stabSub U) (hHZ : H ≤ stabSub Z)
    (h : (FFModel.nat (StatedSL 3 K)).RealizesVia H U Z π) :
    ∃ e : Sec U Z ≃* Multiplicative (Fin 3 → K),
      ∀ (g : ↥(StatedSL 3 K)) (x : Sec U Z),
        e (B5.secHom H hHU hHZ (π g) x) =
          Multiplicative.ofAdd (B5.slAct g (Multiplicative.toAdd (e x))) := by
  obtain ⟨f', hf's, hf'k, hfe'⟩ := exists_secProj h
  have hker : Z.subgroupOf U = f'.ker := by
    ext u
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hf'k u).symm
  let e : Sec U Z ≃* Multiplicative (Fin 3 → K) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f' hf's)
  have he_mk : ∀ u : ↥U, e (QuotientGroup.mk u) = f' u := fun u => rfl
  refine ⟨e, fun g x => ?_⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [B5.secHom_mk H hHU hHZ (π g) u, he_mk, he_mk, hfe' g u]

private theorem secIsoL_of_secMulEquiv {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U Z U' Z' : Subgroup V} (hZU : Z ≤ U) (hZU' : Z' ≤ U')
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hLU' : L ≤ stabSub U') (hLZ' : L ≤ stabSub Z')
    (e : Sec U Z ≃* Sec U' Z')
    (he : ∀ (l : ↥L) (x : Sec U Z), e (B5.secHom L hLU hLZ l x) =
      B5.secHom L hLU' hLZ' l (e x)) :
    SecIsoL L U Z U' Z' := by
  rw [B5.secIsoL_iff]
  have hmk : ∀ (l : ↥L) (u : ↥U) (hu : (l : MulAut V) (u : V) ∈ U),
      (QuotientGroup.mk' (Z.subgroupOf U)) ⟨(l : MulAut V) (u : V), hu⟩ =
        B5.secHom L hLU hLZ l ((QuotientGroup.mk' (Z.subgroupOf U)) u) := by
    intro l u hu
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, B5.secHom_mk]
  have hmk' : ∀ (l : ↥L) (u : ↥U') (hu : (l : MulAut V) (u : V) ∈ U'),
      (QuotientGroup.mk' (Z'.subgroupOf U')) ⟨(l : MulAut V) (u : V), hu⟩ =
        B5.secHom L hLU' hLZ' l ((QuotientGroup.mk' (Z'.subgroupOf U')) u) := by
    intro l u hu
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, B5.secHom_mk]
  refine ⟨hZU, hZU', ?_, ?_, ?_, ?_,
    e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf U)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · intro l u hu
    exact (hLU l.2 u).2 hu
  · intro l z hz
    exact (hLZ l.2 z).2 hz
  · intro l u hu
    exact (hLU' l.2 u).2 hu
  · intro l z hz
    exact (hLZ' l.2 z).2 hz
  · intro u
    show e ((QuotientGroup.mk' (Z.subgroupOf U)) u) = 1 ↔ (u : V) ∈ Z
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  · intro l u m hu hm hum
    have hum' : e ((QuotientGroup.mk' (Z.subgroupOf U)) u) =
        (QuotientGroup.mk' (Z'.subgroupOf U')) m := hum
    show e ((QuotientGroup.mk' (Z.subgroupOf U)) ⟨(l : MulAut V) (u : V), hu⟩) =
      (QuotientGroup.mk' (Z'.subgroupOf U')) ⟨(l : MulAut V) (m : V), hm⟩
    rw [hmk l u hu, he l, hum', hmk' l m hm]

private theorem card_fixV_eq_card_fixK {V : Type} [CommGroup V] {K : Type} [Field K]
    {ρ : ↥(StatedSL 3 K) →* MulAut V} {Φ : V ≃* Multiplicative (Fin 3 → K)}
    {θ : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K)}
    (hΦ : ∀ (g : ↥(StatedSL 3 K)) (v : V),
      Φ (ρ g v) = Multiplicative.ofAdd (B5.slAct (θ g) (Multiplicative.toAdd (Φ v))))
    (H : Subgroup ↥(StatedSL 3 K)) :
    Nat.card ↥(fixV (H.map ρ)) =
      Nat.card ↥(B5.fixK (H.map θ.toMonoidHom)) := by
  have hiff : ∀ v : V, v ∈ fixV (H.map ρ) ↔
      Multiplicative.toAdd (Φ v) ∈ B5.fixK (H.map θ.toMonoidHom) := by
    intro v
    constructor
    · intro hv
      rw [B5.mem_fixK]
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hg
      have h1 : Φ (ρ h v) =
          Multiplicative.ofAdd (B5.slAct (θ h) (Multiplicative.toAdd (Φ v))) := hΦ h v
      rw [show ρ h v = v from hv (ρ h) (Subgroup.mem_map_of_mem ρ hh)] at h1
      exact (Multiplicative.ofAdd.injective h1).symm
    · intro hv
      rw [mem_fixV]
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hg
      apply Φ.injective
      rw [hΦ h v, show B5.slAct (θ h) (Multiplicative.toAdd (Φ v)) =
        Multiplicative.toAdd (Φ v) from
        (B5.mem_fixK.mp hv) (θ h) (Subgroup.mem_map_of_mem θ.toMonoidHom hh)]
      rfl
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨Multiplicative.toAdd (Φ x.1), (hiff x.1).mp x.2⟩
      invFun := fun y => ⟨Φ.symm (Multiplicative.ofAdd y.1), (hiff _).mpr ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  simpa using y.2

private theorem centralizes_of_faithful_sec {W : Type} [CommGroup W]
    {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hfaith : L ⊓ centSec I Z = ⊥)
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hXn : L ⊔ A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {d : MulAut W} (hd : d ∈ L) {a : MulAut W} (ha : a ∈ A)
    (hsame : B5.secHom L hLI hLZ ⟨d, hd⟩ = B5.secHom A hAI hAZ ⟨a, ha⟩) :
    ∀ l ∈ L, (d⁻¹ * a) * l = l * (d⁻¹ * a) := by
  have hXI : L ⊔ A ≤ stabSub I := sup_le hLI hAI
  have hXZ : L ⊔ A ≤ stabSub Z := sup_le hLZ hAZ
  have hyX : d⁻¹ * a ∈ L ⊔ A :=
    (L ⊔ A).mul_mem ((L ⊔ A).inv_mem (Subgroup.mem_sup_left hd))
      (Subgroup.mem_sup_right ha)
  have hAn : ∀ x ∈ L ⊔ A, ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun x hx l hl =>
    (Subgroup.mem_normalizer_iff.mp (hXn hx) l).mp hl
  have hinclL : ∀ (y : MulAut W) (hy : y ∈ L) (hyX : y ∈ L ⊔ A),
      B5.secHom (L ⊔ A) hXI hXZ ⟨y, hyX⟩ = B5.secHom L hLI hLZ ⟨y, hy⟩ :=
    fun y hy hyX => rfl
  have hinclA : ∀ (y : MulAut W) (hy : y ∈ A) (hyX : y ∈ L ⊔ A),
      B5.secHom (L ⊔ A) hXI hXZ ⟨y, hyX⟩ = B5.secHom A hAI hAZ ⟨y, hy⟩ :=
    fun y hy hyX => rfl
  have hyker : B5.secHom (L ⊔ A) hXI hXZ ⟨d⁻¹ * a, hyX⟩ = 1 := by
    have hy : (⟨d⁻¹ * a, hyX⟩ : ↥(L ⊔ A)) =
        (⟨d, Subgroup.mem_sup_left hd⟩ : ↥(L ⊔ A))⁻¹ *
          ⟨a, Subgroup.mem_sup_right ha⟩ := Subtype.ext (by simp)
    rw [hy, map_mul, map_inv, hinclL d hd _, hinclA a ha _, hsame, inv_mul_cancel]
  have hycent : d⁻¹ * a ∈ centSec I Z :=
    (B5.mem_ker_secHom (L ⊔ A) hXI hXZ ⟨_, hyX⟩).1 (MonoidHom.mem_ker.2 hyker)
  intro l hl
  have hmem : d⁻¹ * a * l * (d⁻¹ * a)⁻¹ ∈ L := hAn (d⁻¹ * a) hyX l hl
  have h1 : B5.secHom (L ⊔ A) hXI hXZ ⟨d⁻¹ * a * l * (d⁻¹ * a)⁻¹,
      Subgroup.mem_sup_left hmem⟩ =
      B5.secHom (L ⊔ A) hXI hXZ ⟨l, Subgroup.mem_sup_left hl⟩ := by
    have hy : (⟨d⁻¹ * a * l * (d⁻¹ * a)⁻¹, Subgroup.mem_sup_left hmem⟩ : ↥(L ⊔ A)) =
        ⟨d⁻¹ * a, hyX⟩ * ⟨l, Subgroup.mem_sup_left hl⟩ * ⟨d⁻¹ * a, hyX⟩⁻¹ :=
      Subtype.ext (by simp [mul_assoc])
    rw [hy, map_mul, map_inv, map_mul, hyker]
    simp
  have h2 : B5.secHom L hLI hLZ ⟨d⁻¹ * a * l * (d⁻¹ * a)⁻¹, hmem⟩ =
      B5.secHom L hLI hLZ ⟨l, hl⟩ := by
    rw [← hinclL (d⁻¹ * a * l * (d⁻¹ * a)⁻¹) hmem _,
      ← hinclL l hl (Subgroup.mem_sup_left hl)]
    exact h1
  have hker : (B5.secHom L hLI hLZ).ker = ⊥ := B5.ker_secHom_eq_bot L hLI hLZ hfaith
  have hinj : Function.Injective (B5.secHom L hLI hLZ) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hval : d⁻¹ * a * l * (d⁻¹ * a)⁻¹ = l :=
    congrArg Subtype.val (hinj h2)
  calc (d⁻¹ * a) * l = ((d⁻¹ * a) * l * (d⁻¹ * a)⁻¹) * (d⁻¹ * a) := by group
    _ = l * (d⁻¹ * a) := by rw [hval]

private theorem sq_eq_one_of_secHom_eq {W : Type} [CommGroup W]
    {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    {d : ↥L} {a : ↥A} (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hfaith : L ⊓ centSec I Z = ⊥) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hsq : (B5.secHom A hAI hAZ a) ^ 2 = 1)
    (hsame : B5.secHom L hLI hLZ d = B5.secHom A hAI hAZ a) : d * d = 1 := by
  have hker : (B5.secHom L hLI hLZ).ker = ⊥ := B5.ker_secHom_eq_bot L hLI hLZ hfaith
  have h1 : B5.secHom L hLI hLZ (d * d) = 1 := by
    rw [map_mul, hsame]
    simpa [pow_two] using hsq
  have h2 : d * d ∈ (B5.secHom L hLI hLZ).ker := MonoidHom.mem_ker.2 h1
  rw [hker] at h2
  exact Subgroup.mem_bot.1 h2

private theorem centre_no_involution {K : Type} [Field K] [CharP K 2]
    {g : ↥(StatedSL 3 K)} (hc : g ∈ Subgroup.center ↥(StatedSL 3 K)) (hg : g * g = 1) :
    g = 1 := by
  let φ : (Fin 3 → K) →+ (Fin 3 → K) :=
    { toFun := B5.slAct g
      map_zero' := B5.slAct_zero g
      map_add' := B5.slAct_add g }
  have hφ : ∀ (h : ↥(StatedSL 3 K)) (x : Fin 3 → K),
      φ (B5.slAct h x) = B5.slAct h (φ x) := by
    intro h x
    show B5.slAct g (B5.slAct h x) = B5.slAct h (B5.slAct g x)
    rw [← B5.slAct_mul, ← B5.slAct_mul, Subgroup.mem_center_iff.mp hc h]
  obtain ⟨κ, hκ⟩ := B5.sl3_end_scalar φ hφ
  have hg2 : ∀ x, φ (φ x) = x := by
    intro x
    show B5.slAct g (B5.slAct g x) = x
    rw [← B5.slAct_mul, hg, B5.slAct_one]
  have hκ2 : κ * κ = 1 := by
    have h := hg2 (Pi.single 0 1)
    rw [hκ, hκ] at h
    have h0 := congrFun h 0
    simpa [Pi.smul_apply] using h0
  have hκ1 : κ = 1 := by
    have htwo : (2 : K) = 0 := by
      rw [show (2 : K) = ((2 : ℕ) : K) by norm_num]
      exact CharP.cast_eq_zero K 2
    have h2 : (κ - 1) * (κ - 1) = 0 := by
      have h3 : (κ - 1) * (κ - 1) = κ * κ - (2 : K) * κ + 1 := by ring
      have h4 : (1 : K) + 1 = 0 := by
        rw [← htwo]
        norm_num
      rw [h3, hκ2, htwo, zero_mul, sub_zero, h4]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)
  apply B5.ext_slAct
  intro x
  have h : B5.slAct g x = (1 : K) • x := by
    have h0 := hκ x
    rw [hκ1] at h0
    simpa [φ] using h0
  rw [h, B5.slAct_one, one_smul]

private theorem z_central {W : Type} [CommGroup W]
    {L A : Subgroup (MulAut W)} {d d' : ↥L} {a : ↥A}
    (hy : ∀ l ∈ L, ((d : MulAut W)⁻¹ * a) * l = l * ((d : MulAut W)⁻¹ * a))
    (hy' : ∀ l ∈ L, ((d' : MulAut W)⁻¹ * a) * l = l * ((d' : MulAut W)⁻¹ * a)) :
    ∀ l ∈ L, ((d' : MulAut W)⁻¹ * (d : MulAut W)) * l =
      l * ((d' : MulAut W)⁻¹ * (d : MulAut W)) := by
  have hyinv : ∀ l ∈ L,
      ((d : MulAut W)⁻¹ * a)⁻¹ * l = l * ((d : MulAut W)⁻¹ * a)⁻¹ := by
    intro l hl
    calc ((d : MulAut W)⁻¹ * a)⁻¹ * l
        = ((d : MulAut W)⁻¹ * a)⁻¹ * (l * ((d : MulAut W)⁻¹ * a)) * ((d : MulAut W)⁻¹ * a)⁻¹ := by
          group
      _ = ((d : MulAut W)⁻¹ * a)⁻¹ * (((d : MulAut W)⁻¹ * a) * l) * ((d : MulAut W)⁻¹ * a)⁻¹ := by
          rw [hy l hl]
      _ = l * ((d : MulAut W)⁻¹ * a)⁻¹ := by group
  have hz_eq : ((d' : MulAut W)⁻¹ * (d : MulAut W)) =
      ((d' : MulAut W)⁻¹ * a) * ((d : MulAut W)⁻¹ * a)⁻¹ := by
    rw [mul_inv_rev]
    group
  intro l hl
  rw [hz_eq]
  calc ((d' : MulAut W)⁻¹ * a) * ((d : MulAut W)⁻¹ * a)⁻¹ * l
      = ((d' : MulAut W)⁻¹ * a) * (((d : MulAut W)⁻¹ * a)⁻¹ * l) := by group
    _ = ((d' : MulAut W)⁻¹ * a) * (l * ((d : MulAut W)⁻¹ * a)⁻¹) := by rw [hyinv l hl]
    _ = (((d' : MulAut W)⁻¹ * a) * l) * ((d : MulAut W)⁻¹ * a)⁻¹ := by group
    _ = (l * ((d' : MulAut W)⁻¹ * a)) * ((d : MulAut W)⁻¹ * a)⁻¹ := by rw [hy' l hl]
    _ = l * (((d' : MulAut W)⁻¹ * a) * ((d : MulAut W)⁻¹ * a)⁻¹) := by group

private theorem z_sq {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {d d' : ↥L}
    (hz_cent : ∀ l ∈ L, ((d' : MulAut W)⁻¹ * (d : MulAut W)) * l =
      l * ((d' : MulAut W)⁻¹ * (d : MulAut W)))
    (hd2 : d * d = 1) (hd'2 : d' * d' = 1) :
    (⟨(d' : MulAut W)⁻¹ * (d : MulAut W), L.mul_mem (L.inv_mem d'.2) d.2⟩ : ↥L) *
      (⟨(d' : MulAut W)⁻¹ * (d : MulAut W), L.mul_mem (L.inv_mem d'.2) d.2⟩ : ↥L) = 1 := by
  apply Subtype.ext
  let z : MulAut W := (d' : MulAut W)⁻¹ * (d : MulAut W)
  change z * z = 1
  have h1 : (d : MulAut W) = (d' : MulAut W) * z := by
    show (d : MulAut W) = (d' : MulAut W) * ((d' : MulAut W)⁻¹ * (d : MulAut W))
    group
  have hcomm : (d' : MulAut W) * z = z * (d' : MulAut W) := (hz_cent d' d'.2).symm
  have hkey : (d : MulAut W) * (d : MulAut W) = (d' : MulAut W) * (d' : MulAut W) * (z * z) := by
    rw [h1]
    calc ((d' : MulAut W) * z) * ((d' : MulAut W) * z)
        = (d' : MulAut W) * (z * (d' : MulAut W)) * z := by group
      _ = (d' : MulAut W) * ((d' : MulAut W) * z) * z := by rw [← hcomm]
      _ = (d' : MulAut W) * (d' : MulAut W) * (z * z) := by group
  rw [show (d : MulAut W) * (d : MulAut W) = 1 from congrArg Subtype.val hd2,
    show (d' : MulAut W) * (d' : MulAut W) = 1 from congrArg Subtype.val hd'2] at hkey
  simpa using hkey.symm

private theorem eq_of_centralizing_diffs {W : Type} [CommGroup W]
    {L A : Subgroup (MulAut W)} {K : Type} [Field K] [CharP K 2]
    {d d' : ↥L} {a : ↥A}
    (hy : ∀ l ∈ L, ((d : MulAut W)⁻¹ * a) * l = l * ((d : MulAut W)⁻¹ * a))
    (hy' : ∀ l ∈ L, ((d' : MulAut W)⁻¹ * a) * l = l * ((d' : MulAut W)⁻¹ * a))
    (hd2 : d * d = 1) (hd'2 : d' * d' = 1)
    (π₁e : ↥(StatedSL 3 K) ≃* ↥L) : d = d' := by
  have hz_cent := z_central hy hy'
  have hz_mem : ((d' : MulAut W)⁻¹ * (d : MulAut W)) ∈ L := L.mul_mem (L.inv_mem d'.2) d.2
  let z : ↥L := ⟨(d' : MulAut W)⁻¹ * (d : MulAut W), hz_mem⟩
  have hz_center : z ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (by simpa [z] using (hz_cent (l : MulAut W) l.2).symm)
  have hz2 : z * z = 1 := by simpa [z] using z_sq hz_cent hd2 hd'2
  let gz : ↥(StatedSL 3 K) := π₁e.symm z
  have hgz_center : gz ∈ Subgroup.center ↥(StatedSL 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply π₁e.injective
    rw [map_mul, map_mul, show π₁e gz = z from MulEquiv.apply_symm_apply π₁e z]
    exact Subgroup.mem_center_iff.mp hz_center (π₁e h)
  have hgz2 : gz * gz = 1 := by
    apply π₁e.injective
    rw [map_mul, map_one, show π₁e gz = z from MulEquiv.apply_symm_apply π₁e z]
    exact hz2
  have hz1 : z = 1 := by
    have h : π₁e gz = 1 := by rw [centre_no_involution hgz_center hgz2, map_one]
    rwa [show π₁e gz = z from MulEquiv.apply_symm_apply π₁e z] at h
  have hdd : d = d' := by
    have h1 : (d : MulAut W) = (d' : MulAut W) * (z : MulAut W) := by
      show (d : MulAut W) = (d' : MulAut W) * ((d' : MulAut W)⁻¹ * (d : MulAut W))
      group
    rw [show (z : MulAut W) = 1 from congrArg Subtype.val hz1, mul_one] at h1
    exact Subtype.ext h1
  exact hdd

private theorem secHom_eq_second_of_secHom_eq {W : Type} [CommGroup W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K] [CharP K 2]
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hfaith₁ : L ⊓ centSec I Z = ⊥) (hfaith₂ : L ⊓ centSec I' Z' = ⊥)
    (hA₂ : autSec A I' Z' ≤ autSec L I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z))
    (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    {g : ↥(StatedSL 3 K)} {a : ↥A}
    (hga : B5.secHom L hLI hLZ (π₁e g) = B5.secHom A hAI hAZ a) :
    B5.secHom L hLI' hLZ' (π₁e g) = B5.secHom A hAI' hAZ' a := by
  have hrange : B5.secHom A hAI' hAZ' a ∈ autSec L I' Z' :=
    hA₂ (by rw [← B5.range_secHom A hAI' hAZ']; exact ⟨a, rfl⟩)
  let d' : ↥L := (B5.secEquiv L hLI' hLZ' hfaith₂).symm ⟨_, hrange⟩
  have hd' : B5.secHom L hLI' hLZ' d' = B5.secHom A hAI' hAZ' a := by
    have h1 := B5.secEquiv_apply L hLI' hLZ' hfaith₂ d'
    rw [MulEquiv.apply_symm_apply] at h1
    simpa using h1.symm
  have hXn : L ⊔ A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hAL
  have hy := centralizes_of_faithful_sec hLI hLZ hfaith₁ hAI hAZ hXn (π₁e g).2 a.2 hga
  have hy' : ∀ l ∈ L, ((d' : MulAut W)⁻¹ * a) * l = l * ((d' : MulAut W)⁻¹ * a) :=
    centralizes_of_faithful_sec hLI' hLZ' hfaith₂ hAI' hAZ' hXn d'.2 a.2 hd'
  have hsq₁ : (B5.secHom A hAI hAZ a) ^ 2 = 1 :=
    hAel.2 _ (by rw [← B5.range_secHom A hAI hAZ]; exact ⟨a, rfl⟩)
  have hsq₂ : (B5.secHom A hAI' hAZ' a) ^ 2 = 1 := by
    have hmem : ((a : MulAut W) ^ 2) ∈ A ⊓ centSec I Z := by
      refine ⟨by simpa using A.pow_mem a.2 2, ?_⟩
      have h1 : B5.secHom A hAI hAZ (a ^ 2) = 1 := by
        rw [map_pow, hsq₁]
      simpa using (B5.mem_ker_secHom A hAI hAZ (a ^ 2)).1 (MonoidHom.mem_ker.2 h1)
    have hmem' : ((a : MulAut W) ^ 2) ∈ A ⊓ centSec I' Z' := by rw [← hker]; exact hmem
    have h1 : B5.secHom A hAI' hAZ' (a ^ 2) = 1 := by
      apply MonoidHom.mem_ker.1
      exact (B5.mem_ker_secHom A hAI' hAZ' (a ^ 2)).2 (by simpa using hmem'.2)
    rwa [map_pow] at h1
  have hd2 : (π₁e g) * (π₁e g) = 1 :=
    sq_eq_one_of_secHom_eq hLI hLZ hfaith₁ hAI hAZ hsq₁ hga
  have hd'2 : d' * d' = 1 :=
    sq_eq_one_of_secHom_eq hLI' hLZ' hfaith₂ hAI' hAZ' hsq₂ hd'
  have hdd : π₁e g = d' := eq_of_centralizing_diffs hy hy' hd2 hd'2 π₁e
  rw [hdd]
  exact hd'

private theorem card_autSec_eq_of_centSec_eq {V : Type} [CommGroup V] [Finite V]
    {A : Subgroup (MulAut V)} {W U W' U' : Subgroup V}
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U)
    (hAW' : A ≤ stabSub W') (hAU' : A ≤ stabSub U')
    (hker : A ⊓ centSec W U = A ⊓ centSec W' U') :
    Nat.card ↥(autSec A W U) = Nat.card ↥(autSec A W' U') := by
  have h1 := card_autSec_mul hAW hAU
  have h2 := card_autSec_mul hAW' hAU'
  rw [hker] at h1
  have hne : Nonempty ↥(A ⊓ centSec W' U') := ⟨⟨1, (A ⊓ centSec W' U').one_mem⟩⟩
  have hfin : Finite ↥(A ⊓ centSec W' U') :=
    Finite.of_injective (fun x => Subtype.val x) (fun x y h => Subtype.ext h)
  exact Nat.eq_of_mul_eq_mul_right
    (@Nat.card_pos ↥(A ⊓ centSec W' U') hne hfin) (h1.trans h2.symm)

private theorem map_comap_autSec {V : Type} [CommGroup V]
    {L A : Subgroup (MulAut V)} {W U : Subgroup V} {K : Type} [Field K]
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U)
    (hA : autSec A W U ≤ autSec L W U) :
    ((autSec A W U).comap ((B5.secHom L hLW hLU).comp π₁e.toMonoidHom)).map
      ((B5.secHom L hLW hLU).comp π₁e.toMonoidHom) = autSec A W U := by
  have hrange : ((B5.secHom L hLW hLU).comp π₁e.toMonoidHom).range = autSec L W U := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ π₁e.surjective,
      Subgroup.map_top, B5.range_secHom]
  rw [Subgroup.map_comap_eq, inf_eq_right.mpr (hA.trans hrange.ge)]

private theorem card_comap_autSec {V : Type} [CommGroup V]
    {L A : Subgroup (MulAut V)} {W U : Subgroup V} {K : Type} [Field K]
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U) (hfaith : L ⊓ centSec W U = ⊥)
    (hA : autSec A W U ≤ autSec L W U) :
    Nat.card ↥((autSec A W U).comap ((B5.secHom L hLW hLU).comp π₁e.toMonoidHom)) =
      Nat.card ↥(autSec A W U) := by
  have hinj : Function.Injective ((B5.secHom L hLW hLU).comp π₁e.toMonoidHom) :=
    ((MonoidHom.ker_eq_bot_iff _).mp (B5.ker_secHom_eq_bot L hLW hLU hfaith)).comp
      π₁e.injective
  have h := Subgroup.card_map_of_injective (f := (B5.secHom L hLW hLU).comp π₁e.toMonoidHom)
    hinj (K := (autSec A W U).comap ((B5.secHom L hLW hLU).comp π₁e.toMonoidHom))
  rw [map_comap_autSec hLW hLU hA] at h
  exact h.symm

private theorem comap_eq_of_two_sections {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K] [Finite K]
    [CharP K 2]
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hfaith₁ : L ⊓ centSec I Z = ⊥) (hfaith₂ : L ⊓ centSec I' Z' = ⊥)
    (hA₁ : autSec A I Z ≤ autSec L I Z)
    (hA₂ : autSec A I' Z' ≤ autSec L I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z))
    (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z') :
    (autSec A I Z).comap ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) =
      (autSec A I' Z').comap ((B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom) := by
  let ρ₁ : ↥(StatedSL 3 K) →* MulAut (Sec I Z) :=
    (B5.secHom L hLI hLZ).comp π₁e.toMonoidHom
  let ρ₂ : ↥(StatedSL 3 K) →* MulAut (Sec I' Z') :=
    (B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom
  have hcard₁ : Nat.card ↥((autSec A I Z).comap ρ₁) = Nat.card ↥(autSec A I Z) :=
    card_comap_autSec hLI hLZ hfaith₁ hA₁
  have hcard₂ : Nat.card ↥((autSec A I' Z').comap ρ₂) = Nat.card ↥(autSec A I' Z') :=
    card_comap_autSec hLI' hLZ' hfaith₂ hA₂
  have hcardAA : Nat.card ↥(autSec A I Z) = Nat.card ↥(autSec A I' Z') :=
    card_autSec_eq_of_centSec_eq hAI hAZ hAI' hAZ' hker
  have hle : (autSec A I Z).comap ρ₁ ≤ (autSec A I' Z').comap ρ₂ := by
    intro g hg
    rw [Subgroup.mem_comap] at hg ⊢
    rw [← B5.range_secHom A hAI' hAZ']
    have hg' : ρ₁ g ∈ (B5.secHom A hAI hAZ).range := by
      rw [B5.range_secHom]
      exact hg
    obtain ⟨a, ha⟩ := hg'
    have hga : B5.secHom L hLI hLZ (π₁e g) = B5.secHom A hAI hAZ a := by
      simpa [ρ₁] using ha.symm
    have h2 := secHom_eq_second_of_secHom_eq hAL hLI hLZ hLI' hLZ' hAI hAZ hAI' hAZ'
      hfaith₁ hfaith₂ hA₂ hAel hker hga
    exact ⟨a, by simpa [ρ₂] using h2.symm⟩
  have hfin : Finite ↥((autSec A I' Z').comap ρ₂) := Subtype.finite
  refine @Subgroup.eq_of_le_of_card_ge ↥(StatedSL 3 K) _ _ _ hfin hle ?_
  rw [hcard₁, hcard₂]
  exact hcardAA.ge

private noncomputable def invTransposeHom (K : Type) [Field K] :
    ↥(StatedSL 3 K) →* ↥(StatedSL 3 K) :=
  (specialLinearGroupEquivStatedSL 3 K).toMonoidHom.comp
    ((CFSG.Quasithin.MS93.transposeInv).comp
      (specialLinearGroupEquivStatedSL 3 K).symm.toMonoidHom)

private theorem invTransposeHom_involutive {K : Type} [Field K] (g : ↥(StatedSL 3 K)) :
    invTransposeHom K (invTransposeHom K g) = g := by
  simp [invTransposeHom, CFSG.Quasithin.MS93.transposeInv_transposeInv]

private noncomputable def invTransposeSL (K : Type) [Field K] :
    ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K) :=
  MulEquiv.ofBijective (invTransposeHom K)
    ⟨fun a b h => by
        have h' := congrArg (invTransposeHom K) h
        simpa [invTransposeHom_involutive] using h',
      fun y => ⟨invTransposeHom K y, invTransposeHom_involutive y⟩⟩

private theorem invTransposeSL_coe {K : Type} [Field K] (g : ↥(StatedSL 3 K)) :
    (((invTransposeSL K g : ↥(StatedSL 3 K)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      ((((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ := by
  let eSL := specialLinearGroupEquivStatedSL 3 K
  have h1 : invTransposeSL K g = eSL (CFSG.Quasithin.MS93.transposeInv (eSL.symm g)) := by
    simp [invTransposeSL, invTransposeHom, eSL]
  rw [h1, specialLinearGroupEquivStatedSL_coe,
    CFSG.Quasithin.MS93.coe_transposeInv, CFSG.Quasithin.MS93.dualMat,
    Matrix.transpose_inj]
  rw [show ((eSL.symm g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) = eSL.symm (g⁻¹) from
    (map_inv eSL.symm g).symm]
  rw [← specialLinearGroupEquivStatedSL_coe 3 K (eSL.symm (g⁻¹)),
    MulEquiv.apply_symm_apply]

private theorem secIsoL_of_nat_module_eq {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K]
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hZI : Z ≤ I) (hZI' : Z' ≤ I')
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    {e₁ : Sec I Z ≃* Multiplicative (Fin 3 → K)}
    (he₁ : ∀ (h : ↥(StatedSL 3 K)) (x : Sec I Z),
      e₁ (B5.secHom L hLI hLZ (π₁e h) x) =
        Multiplicative.ofAdd (B5.slAct h (Multiplicative.toAdd (e₁ x))))
    {ρ : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (Sec I' Z')}
    (hρ : ∀ g, ρ g = B5.secHom L hLI' hLZ'
      (π₁e ((specialLinearGroupEquivStatedSL 3 K) g)))
    {β : Sec I' Z' ≃* Multiplicative (Fin 3 → K)}
    (hβ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) K) (v : Sec I' Z'),
      β (ρ g v) = Multiplicative.ofAdd
        (((g : Matrix (Fin 3) (Fin 3) K)) *ᵥ Multiplicative.toAdd (β v))) :
    SecIsoL L I Z I' Z' := by
  let F : Sec I Z ≃* Sec I' Z' := e₁.trans β.symm
  refine secIsoL_of_secMulEquiv hZI hZI' hLI hLZ hLI' hLZ' F ?_
  intro l x
  let h : ↥(StatedSL 3 K) := π₁e.symm l
  let g : Matrix.SpecialLinearGroup (Fin 3) K := (specialLinearGroupEquivStatedSL 3 K).symm h
  have hπ : π₁e h = l := MulEquiv.apply_symm_apply π₁e l
  have hg : (specialLinearGroupEquivStatedSL 3 K) g = h :=
    MulEquiv.apply_symm_apply _ h
  have hmat : ((g : Matrix (Fin 3) (Fin 3) K)) =
      (((h : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← specialLinearGroupEquivStatedSL_coe 3 K g, hg]
  change β.symm (e₁ (B5.secHom L hLI hLZ l x)) =
    B5.secHom L hLI' hLZ' l (β.symm (e₁ x))
  have h1 : e₁ (B5.secHom L hLI hLZ l x) =
      Multiplicative.ofAdd (B5.slAct h (Multiplicative.toAdd (e₁ x))) := by
    rw [← hπ]
    exact he₁ h x
  have h2 : β (B5.secHom L hLI' hLZ' l (β.symm (e₁ x))) =
      Multiplicative.ofAdd (B5.slAct h (Multiplicative.toAdd (e₁ x))) := by
    have hρg : ρ g = B5.secHom L hLI' hLZ' l := by rw [hρ g, hg, hπ]
    have h := hβ g (β.symm (e₁ x))
    rw [hρg, MulEquiv.apply_symm_apply, hmat] at h
    simpa [B5.slAct] using h
  rw [h1, ← h2, MulEquiv.symm_apply_apply]

private theorem exists_dual_D {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K] [Finite K]
    [CharP K 2] {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hfaith₁ : L ⊓ centSec I Z = ⊥) (hfaith₂ : L ⊓ centSec I' Z' = ⊥)
    (hA₁ : autSec A I Z ≤ autSec L I Z) (hA₂ : autSec A I' Z' ≤ autSec L I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z))
    (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z') :
    ∃ D : Subgroup ↥(StatedSL 3 K),
      D.map ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) = autSec A I Z ∧
      D.map ((B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom) = autSec A I' Z' := by
  let ρ₁ : ↥(StatedSL 3 K) →* MulAut (Sec I Z) := (B5.secHom L hLI hLZ).comp π₁e.toMonoidHom
  let ρ₂ : ↥(StatedSL 3 K) →* MulAut (Sec I' Z') := (B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom
  let D : Subgroup ↥(StatedSL 3 K) := (autSec A I Z).comap ρ₁
  have hinjL₁ : Function.Injective (B5.secHom L hLI hLZ) :=
    (MonoidHom.ker_eq_bot_iff _).mp (B5.ker_secHom_eq_bot L hLI hLZ hfaith₁)
  have hρ₁inj : Function.Injective ρ₁ := hinjL₁.comp π₁e.injective
  have hrange₁ : ρ₁.range = autSec L I Z := by
    simp only [ρ₁]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ π₁e.surjective,
      Subgroup.map_top, B5.range_secHom]
  have hrange₂ : ρ₂.range = autSec L I' Z' := by
    simp only [ρ₂]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ π₁e.surjective,
      Subgroup.map_top, B5.range_secHom]
  have hDmap₁ : D.map ρ₁ = autSec A I Z := by
    simp only [D]
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr (hA₁.trans hrange₁.ge)]
  have hDeq : D = (autSec A I' Z').comap ρ₂ := by
    simp only [D]
    exact comap_eq_of_two_sections hAL hLI hLZ hLI' hLZ' hAI hAZ hAI' hAZ' hfaith₁ hfaith₂
      hA₁ hA₂ hAel hker
  have hDmap₂ : D.map ρ₂ = autSec A I' Z' := by
    rw [hDeq, Subgroup.map_comap_eq, inf_eq_right.mpr (hA₂.trans hrange₂.ge)]
  have hρ₁inj : Function.Injective ρ₁ := hinjL₁.comp π₁e.injective
  exact ⟨D, hDmap₁, hDmap₂⟩

private theorem dual_D_sq_comm {W : Type} [CommGroup W] {L A : Subgroup (MulAut W)}
    {I Z : Subgroup W} {K : Type} [Field K] {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hfaith₁ : L ⊓ centSec I Z = ⊥)
    (hAel : IsElemAbelian2 (autSec A I Z)) (D : Subgroup ↥(StatedSL 3 K))
    (hDmap₁ : D.map ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) = autSec A I Z) :
    (∀ g ∈ D, g * g = 1) ∧ (∀ g ∈ D, ∀ h ∈ D, g * h = h * g) := by
  have hρ₁inj : Function.Injective ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) :=
    ((MonoidHom.ker_eq_bot_iff _).mp (B5.ker_secHom_eq_bot L hLI hLZ hfaith₁)).comp
      π₁e.injective
  have hsq : ∀ g ∈ D, g * g = 1 := by
    intro g hg
    have h1 : ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) (g * g) = 1 := by
      rw [map_mul]
      have hmem : ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) g ∈ autSec A I Z := by
        rw [← hDmap₁]
        exact Subgroup.mem_map_of_mem _ hg
      simpa [pow_two] using hAel.2 _ hmem
    exact hρ₁inj (by simpa using h1)
  refine ⟨hsq, ?_⟩
  intro g hg h hh
  apply hρ₁inj
  rw [map_mul, map_mul]
  exact hAel.1 _ (by rw [← hDmap₁]; exact Subgroup.mem_map_of_mem _ hg)
    _ (by rw [← hDmap₁]; exact Subgroup.mem_map_of_mem _ hh)

private theorem card_Sec_nat {K : Type} [Field K] {V : Type} [CommGroup V]
    {U Z : Subgroup V} (e : Sec U Z ≃* Multiplicative (Fin 3 → K)) :
    Nat.card (Sec U Z) = Nat.card K ^ 3 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_fin]

private theorem card_fixK_eq {K : Type} [Field K] (D : Subgroup ↥(StatedSL 3 K)) :
    Nat.card ↥(B5.fixK D) = Nat.card K ^ Module.finrank K (B5.fixK D) :=
  Module.natCard_eq_pow_finrank

private theorem card_pow_rank {K : Type} [Field K]
    (D : Subgroup ↥(StatedSL 3 K)) [Finite ↥D] (hsq : ∀ g ∈ D, g * g = 1) :
    Nat.card ↥D = 2 ^ rk ↥D :=
  card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one fun x => by
    apply Subtype.ext
    simpa [pow_two] using hsq (x : ↥(StatedSL 3 K)) x.2)

private theorem dual_card_fix {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K] [Finite K]
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (hfaith₁ : L ⊓ centSec I Z = ⊥)
    {e₁ : Sec I Z ≃* Multiplicative (Fin 3 → K)}
    (he₁ : ∀ (h : ↥(StatedSL 3 K)) (x : Sec I Z),
      e₁ (B5.secHom L hLI hLZ (π₁e h) x) =
        Multiplicative.ofAdd (B5.slAct h (Multiplicative.toAdd (e₁ x))))
    {e₂ : Sec I' Z' ≃* Multiplicative (Fin 3 → K)}
    (he₂ : ∀ (g : ↥(StatedSL 3 K)) (x : Sec I' Z'),
      e₂ (B5.secHom L hLI' hLZ' (π₁e g) x) =
        Multiplicative.ofAdd (B5.slAct (invTransposeSL K g) (Multiplicative.toAdd (e₂ x))))
    (D : Subgroup ↥(StatedSL 3 K)) [Finite ↥D]
    (hDmap₁ : D.map ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) = autSec A I Z)
    (hDmap₂ : D.map ((B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom) = autSec A I' Z') :
    Nat.card ↥D = Nat.card ↥(autSec A I Z) ∧
      Nat.card ↥(fixV (autSec A I Z)) = Nat.card ↥(B5.fixK D) ∧
      Nat.card ↥(fixV (autSec A I' Z')) =
        Nat.card ↥(B5.fixK (D.map (invTransposeSL K).toMonoidHom)) := by
  have hρ₁inj : Function.Injective ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) :=
    ((MonoidHom.ker_eq_bot_iff _).mp (B5.ker_secHom_eq_bot L hLI hLZ hfaith₁)).comp
      π₁e.injective
  have hcardD : Nat.card ↥D = Nat.card ↥(autSec A I Z) := by
    have h := Subgroup.card_map_of_injective
      (f := (B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) hρ₁inj (K := D)
    rw [hDmap₁] at h
    exact h.symm
  have hfix₁ : Nat.card ↥(fixV (autSec A I Z)) = Nat.card ↥(B5.fixK D) := by
    rw [← hDmap₁]
    have h := card_fixV_eq_card_fixK (ρ := (B5.secHom L hLI hLZ).comp π₁e.toMonoidHom)
      (θ := MulEquiv.refl ↥(StatedSL 3 K)) he₁ D
    simpa using h
  have hfix₂ : Nat.card ↥(fixV (autSec A I' Z')) =
      Nat.card ↥(B5.fixK (D.map (invTransposeSL K).toMonoidHom)) := by
    rw [← hDmap₂]
    exact card_fixV_eq_card_fixK he₂ D
  exact ⟨hcardD, hfix₁, hfix₂⟩

private theorem dual_log_bound {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K] [Finite K]
    [CharP K 2] {a : ℕ} (hKcard : Nat.card K = 2 ^ a)
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (hfaith₁ : L ⊓ centSec I Z = ⊥)
    {e₁ : Sec I Z ≃* Multiplicative (Fin 3 → K)}
    (he₁ : ∀ (h : ↥(StatedSL 3 K)) (x : Sec I Z),
      e₁ (B5.secHom L hLI hLZ (π₁e h) x) =
        Multiplicative.ofAdd (B5.slAct h (Multiplicative.toAdd (e₁ x))))
    {e₂ : Sec I' Z' ≃* Multiplicative (Fin 3 → K)}
    (he₂ : ∀ (g : ↥(StatedSL 3 K)) (x : Sec I' Z'),
      e₂ (B5.secHom L hLI' hLZ' (π₁e g) x) =
        Multiplicative.ofAdd (B5.slAct (invTransposeSL K g) (Multiplicative.toAdd (e₂ x))))
    (D : Subgroup ↥(StatedSL 3 K))
    (hDmap₁ : D.map ((B5.secHom L hLI hLZ).comp π₁e.toMonoidHom) = autSec A I Z)
    (hDmap₂ : D.map ((B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom) = autSec A I' Z')
    (hsq : ∀ g ∈ D, g * g = 1)
    (hcost : Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤ Nat.card ↥(autSec A I Z) *
      Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(fixV (autSec A I' Z'))) :
    6 * a ≤ rk ↥D + a * Module.finrank K (B5.fixK D) +
        a * Module.finrank K (B5.fixK (D.map (invTransposeSL K).toMonoidHom)) := by
  obtain ⟨hcardD, hfix₁, hfix₂⟩ := dual_card_fix (K := K) (π₁e := π₁e)
    hLI hLZ hLI' hLZ' hfaith₁ he₁ he₂ D hDmap₁ hDmap₂
  have hsec₁ := card_Sec_nat e₁
  have hsec₂ := card_Sec_nat e₂
  have hcardF := card_fixK_eq D
  have hcardF' := card_fixK_eq (D.map (invTransposeSL K).toMonoidHom)
  have hDpow := card_pow_rank D hsq
  have h := hcost
  rw [← hcardD, hfix₁, hfix₂, hsec₁, hsec₂, hcardF, hcardF', hDpow, hKcard] at h
  have h6 : (2 ^ a) ^ 3 * (2 ^ a) ^ 3 = 2 ^ (6 * a) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hR : 2 ^ rk ↥D * (2 ^ a) ^ Module.finrank K (B5.fixK D) *
      (2 ^ a) ^ Module.finrank K (B5.fixK (D.map (invTransposeSL K).toMonoidHom)) =
      2 ^ (rk ↥D + a * Module.finrank K (B5.fixK D) +
        a * Module.finrank K (B5.fixK (D.map (invTransposeSL K).toMonoidHom))) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  rw [h6, hR] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

private theorem dual_pair_bound
    {K : Type} [Field K] [Finite K] [CharP K 2] {a : ℕ} (hKcard : Nat.card K = 2 ^ a)
    (D : Subgroup ↥(StatedSL 3 K)) (hsq : ∀ g ∈ D, g * g = 1)
    (hcomm : ∀ g ∈ D, ∀ h ∈ D, g * h = h * g) :
    3 * rk ↥D ≤ 2 * (3 * a - a * Module.finrank K (B5.fixK D) +
      (3 * a - a * Module.finrank K (B5.fixK (D.map (invTransposeSL K).toMonoidHom)))) := by
  have hpair := B5.sl3_pair_bound hKcard D hsq hcomm (invTransposeSL K) 1 (RingEquiv.refl K)
    (fun g => by
      rw [invTransposeSL_coe]
      rw [show (⇑(RingEquiv.refl K) : K → K) = id from rfl, Matrix.map_id]
      simp)
  have hd3 : Module.finrank K (B5.fixK D) ≤ 3 := by
    simpa [Module.finrank_fin_fun] using Submodule.finrank_le (B5.fixK D)
  have hd3' : Module.finrank K (B5.fixK (D.map (invTransposeSL K).toMonoidHom)) ≤ 3 := by
    simpa [Module.finrank_fin_fun] using
      Submodule.finrank_le (B5.fixK (D.map (invTransposeSL K).toMonoidHom))
  rw [Nat.mul_sub a 3 (Module.finrank K (B5.fixK D)),
    Nat.mul_sub a 3 (Module.finrank K (B5.fixK (D.map (invTransposeSL K).toMonoidHom)))] at hpair
  rw [Nat.mul_comm a 3] at hpair
  exact hpair

private theorem rank_eq_zero_of_dual_bounds {a r d d' : ℕ} (hd : d ≤ 3) (hd' : d' ≤ 3)
    (hlog : 6 * a ≤ r + a * d + a * d')
    (hpair : 3 * r ≤ 2 * (3 * a - a * d + (3 * a - a * d'))) : r = 0 := by
  have hc : a * d ≤ 3 * a := by
    rw [mul_comm 3 a]
    exact Nat.mul_le_mul_left a hd
  have hc' : a * d' ≤ 3 * a := by
    rw [mul_comm 3 a]
    exact Nat.mul_le_mul_left a hd'
  omega

private theorem false_of_nat_dual_true {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K] [Finite K]
    [CharP K 2] {a : ℕ} (hKcard : Nat.card K = 2 ^ a)
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hfaith₁ : L ⊓ centSec I Z = ⊥) (hfaith₂ : L ⊓ centSec I' Z' = ⊥)
    (hA₁ : autSec A I Z ≤ autSec L I Z) (hA₂ : autSec A I' Z' ≤ autSec L I' Z')
    (hAnc : ¬ A ≤ centSec I Z) (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z))
    {e₁ : Sec I Z ≃* Multiplicative (Fin 3 → K)}
    (he₁ : ∀ (h : ↥(StatedSL 3 K)) (x : Sec I Z),
      e₁ (B5.secHom L hLI hLZ (π₁e h) x) =
        Multiplicative.ofAdd (B5.slAct h (Multiplicative.toAdd (e₁ x))))
    {e₂ : Sec I' Z' ≃* Multiplicative (Fin 3 → K)}
    (he₂ : ∀ (g : ↥(StatedSL 3 K)) (x : Sec I' Z'),
      e₂ (B5.secHom L hLI' hLZ' (π₁e g) x) =
        Multiplicative.ofAdd (B5.slAct (invTransposeSL K g) (Multiplicative.toAdd (e₂ x))))
    (hcost : Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤ Nat.card ↥(autSec A I Z) *
      Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(fixV (autSec A I' Z'))) : False := by
  obtain ⟨D, hDmap₁, hDmap₂⟩ := exists_dual_D (K := K) (π₁e := π₁e)
    hAL hLI hLZ hLI' hLZ' hAI hAZ hAI'
    hAZ' hfaith₁ hfaith₂ hA₁ hA₂ hAel hker
  obtain ⟨hsq, hcomm⟩ := dual_D_sq_comm (K := K) (π₁e := π₁e) hLI hLZ hfaith₁ hAel D hDmap₁
  have hrk0 : rk ↥D = 0 := rank_eq_zero_of_dual_bounds
    (by simpa [Module.finrank_fin_fun] using Submodule.finrank_le (B5.fixK D))
    (by simpa [Module.finrank_fin_fun] using
      Submodule.finrank_le (B5.fixK (D.map (invTransposeSL K).toMonoidHom)))
    (dual_log_bound hKcard hLI hLZ hLI' hLZ' hfaith₁ he₁ he₂ D hDmap₁ hDmap₂ hsq hcost)
    (dual_pair_bound hKcard D hsq hcomm)
  have hDbot : D = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [card_pow_rank D hsq, hrk0, pow_zero]
  have haut : autSec A I Z = ⊥ := by
    rw [← hDmap₁, hDbot, Subgroup.map_bot]
  exact B69.autSec_ne_bot hAI hAZ hAnc haut

private theorem dualMat_eq_invTransposeSL {K : Type} [Field K] (g : ↥(StatedSL 3 K)) :
    CFSG.Quasithin.MS93.dualMat
        ((specialLinearGroupEquivStatedSL 3 K).symm g) =
      (((invTransposeSL K g : ↥(StatedSL 3 K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
  rw [CFSG.Quasithin.MS93.dualMat, invTransposeSL_coe]
  congr 1
  rw [← map_inv,
    ← specialLinearGroupEquivStatedSL_coe 3 K
      ((specialLinearGroupEquivStatedSL 3 K).symm (g⁻¹)),
    MulEquiv.apply_symm_apply]

private theorem he_of_natAct_true {K : Type} [Field K] {V : Type} [CommGroup V]
    {β : V ≃* Multiplicative (Fin 3 → K)}
    {ρ : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut V}
    (hβ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) K) (v : V),
      β (ρ g v) = Multiplicative.ofAdd
        (CFSG.Quasithin.MS93.natAct true g *ᵥ Multiplicative.toAdd (β v)))
    (ρ₂ : ↥(StatedSL 3 K) →* MulAut V)
    (hρ : ∀ g : ↥(StatedSL 3 K),
      ρ ((specialLinearGroupEquivStatedSL 3 K).symm g) = ρ₂ g) :
    ∀ (g : ↥(StatedSL 3 K)) (v : V), β (ρ₂ g v) =
      Multiplicative.ofAdd (B5.slAct (invTransposeSL K g) (Multiplicative.toAdd (β v))) := by
  intro g v
  have h := hβ ((specialLinearGroupEquivStatedSL 3 K).symm g) v
  rw [hρ g, CFSG.Quasithin.MS93.natAct_true,
    dualMat_eq_invTransposeSL g] at h
  simpa [B5.slAct] using h

private theorem classification_he {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I' Z' : Subgroup W} {K K' : Type}
    [Field K] [Finite K] [Field K'] [Finite K']
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L} {π₂ : ↥(StatedSL 3 K') →* ↥L}
    {eSL : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(StatedSL 3 K)}
    {θ' : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K')}
    {ρ : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (Sec I' Z')}
    {e₂ : Sec I' Z' ≃* Multiplicative (Fin 3 → K')}
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (hρ : ∀ g, ρ g = B5.secHom L hLI' hLZ' (π₁e (eSL g)))
    (hπθ : ∀ g : ↥(StatedSL 3 K), π₂ (θ' g) = π₁e g)
    (he₂₀ : ∀ (g : ↥(StatedSL 3 K')) (x : Sec I' Z'),
      e₂ (B5.secHom L hLI' hLZ' (π₂ g) x) =
        Multiplicative.ofAdd (B5.slAct g (Multiplicative.toAdd (e₂ x)))) :
    ∀ (g : Matrix.SpecialLinearGroup (Fin 3) K) (v : Sec I' Z'),
      e₂ (ρ g v) = Multiplicative.ofAdd
        (((((specialLinearGroupEquivStatedSL 3 K').symm (θ' (eSL g)) :
            Matrix.SpecialLinearGroup (Fin 3) K') :
          Matrix (Fin 3) (Fin 3) K') *ᵥ Multiplicative.toAdd (e₂ v))) := by
  intro g v
  have h1 := he₂₀ (θ' (eSL g)) v
  have h2 : π₂ (θ' (eSL g)) = π₁e (eSL g) := hπθ (eSL g)
  have hρg : ρ g v = B5.secHom L hLI' hLZ' (π₂ (θ' (eSL g))) v := by
    rw [hρ g, h2]
  rw [hρg, h1]
  exact congrArg Multiplicative.ofAdd (by
    rw [B5.slAct]
    have hmat : ((((θ' (eSL g) : ↥(StatedSL 3 K')) : GL (Fin 3) K') :
        Matrix (Fin 3) (Fin 3) K')) =
        ((((specialLinearGroupEquivStatedSL 3 K').symm (θ' (eSL g)) :
            Matrix.SpecialLinearGroup (Fin 3) K') :
          Matrix (Fin 3) (Fin 3) K')) := by
      have hx : ((specialLinearGroupEquivStatedSL 3 K')
          ((specialLinearGroupEquivStatedSL 3 K').symm
            (θ' (eSL g))) : ↥(StatedSL 3 K')) = θ' (eSL g) :=
        MulEquiv.apply_symm_apply _ _
      conv_lhs =>
        arg 1
        arg 1
        rw [← hx]
      simpa using
        (specialLinearGroupEquivStatedSL_coe 3 K'
          ((specialLinearGroupEquivStatedSL 3 K').symm (θ' (eSL g))))
    rw [hmat])

private theorem secIsoL_of_classified {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {K : Type} [Field K] [Finite K]
    [CharP K 2] {a : ℕ} (hKcard : Nat.card K = 2 ^ a)
    {π₁e : ↥(StatedSL 3 K) ≃* ↥L}
    {e₁ : Sec I Z ≃* Multiplicative (Fin 3 → K)}
    (hZI : Z ≤ I) (hZI' : Z' ≤ I')
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hLI' : L ≤ stabSub I') (hLZ' : L ≤ stabSub Z')
    (he₁ : ∀ (h : ↥(StatedSL 3 K)) (x : Sec I Z),
      e₁ (B5.secHom L hLI hLZ (π₁e h) x) =
        Multiplicative.ofAdd (B5.slAct h (Multiplicative.toAdd (e₁ x))))
    {ρ : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (Sec I' Z')}
    (hρ : ∀ g, ρ g = B5.secHom L hLI' hLZ' (π₁e ((specialLinearGroupEquivStatedSL 3 K) g)))
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hfaith₁ : L ⊓ centSec I Z = ⊥) (hfaith₂ : L ⊓ centSec I' Z' = ⊥)
    (hA₁ : autSec A I Z ≤ autSec L I Z) (hA₂ : autSec A I' Z' ≤ autSec L I' Z')
    (hAnc : ¬ A ≤ centSec I Z) (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z))
    (hcost : Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤ Nat.card ↥(autSec A I Z) *
      Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(fixV (autSec A I' Z')))
    (dual : Bool) (β : Sec I' Z' ≃* Multiplicative (Fin 3 → K))
    (hβ : ∀ (g : Matrix.SpecialLinearGroup (Fin 3) K) (v : Sec I' Z'),
      β (ρ g v) = Multiplicative.ofAdd
        (CFSG.Quasithin.MS93.natAct dual g *ᵥ Multiplicative.toAdd (β v))) :
    SecIsoL L I Z I' Z' := by
  cases dual with
  | false =>
      exact secIsoL_of_nat_module_eq (π₁e := π₁e) hZI hZI' hLI hLZ hLI' hLZ' he₁ hρ
        (fun g v => hβ g v)
  | true =>
      exfalso
      have hρ₂ : ∀ g : ↥(StatedSL 3 K),
          ρ ((specialLinearGroupEquivStatedSL 3 K).symm g) =
            ((B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom) g := by
        intro g
        rw [hρ ((specialLinearGroupEquivStatedSL 3 K).symm g),
          show (specialLinearGroupEquivStatedSL 3 K)
              ((specialLinearGroupEquivStatedSL 3 K).symm g) = g from
            MulEquiv.apply_symm_apply _ g]
        rfl
      have heβ' : ∀ (g : ↥(StatedSL 3 K)) (v : Sec I' Z'),
          β (B5.secHom L hLI' hLZ' (π₁e g) v) =
            Multiplicative.ofAdd (B5.slAct (invTransposeSL K g) (Multiplicative.toAdd (β v))) :=
        he_of_natAct_true hβ (ρ₂ := (B5.secHom L hLI' hLZ').comp π₁e.toMonoidHom) hρ₂
      exact false_of_nat_dual_true (π₁e := π₁e) hKcard hAL hLI hLZ hLI' hLZ'
        hAI hAZ hAI' hAZ' hfaith₁ hfaith₂ hA₁ hA₂ hAnc hker hAel he₁ heβ' hcost

private theorem secIsoL_of_two_realizations {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W}
    {K K' : Type} [Field K] [Finite K] [CharP K 2] [Field K'] [Finite K'] [CharP K' 2]
    {a : ℕ} (hKcard : Nat.card K = 2 ^ a)
    {π₁ : ↥(StatedSL 3 K) →* ↥L} {π₂ : ↥(StatedSL 3 K') →* ↥L}
    (hRV₁ : (FFModel.nat (StatedSL 3 K)).RealizesVia L I Z π₁)
    (hRV₂ : (FFModel.nat (StatedSL 3 K')).RealizesVia L I' Z' π₂)
    (hfaith₁ : L ⊓ centSec I Z = ⊥) (hfaith₂ : L ⊓ centSec I' Z' = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hA₁ : autSec A I Z ≤ autSec L I Z) (hA₂ : autSec A I' Z' ≤ autSec L I' Z')
    (hAnc : ¬ A ≤ centSec I Z) (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z))
    (hcost : Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤ Nat.card ↥(autSec A I Z) *
      Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(fixV (autSec A I' Z'))) :
    SecIsoL L I Z I' Z' := by
  have hLI : L ≤ stabSub I := B1.le_stabSub_of_invariant
    (fun a ha u hu => hRV₁.2.2.2.1 ⟨a, ha⟩ u hu)
  have hLZ : L ≤ stabSub Z := B1.le_stabSub_of_invariant
    (fun a ha z hz => hRV₁.2.2.2.2.1 ⟨a, ha⟩ z hz)
  have hLI' : L ≤ stabSub I' := B1.le_stabSub_of_invariant
    (fun a ha u hu => hRV₂.2.2.2.1 ⟨a, ha⟩ u hu)
  have hLZ' : L ≤ stabSub Z' := B1.le_stabSub_of_invariant
    (fun a ha z hz => hRV₂.2.2.2.2.1 ⟨a, ha⟩ z hz)
  let π₁e : ↥(StatedSL 3 K) ≃* ↥L := MulEquiv.ofBijective π₁
    ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hRV₁, hRV₁.1⟩
  let π₂e : ↥(StatedSL 3 K') ≃* ↥L := MulEquiv.ofBijective π₂
    ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hRV₂, hRV₂.1⟩
  obtain ⟨e₁, he₁⟩ := exists_coord_sec hLI hLZ hRV₁
  obtain ⟨e₂, he₂₀⟩ := exists_coord_sec hLI' hLZ' hRV₂
  let eSL := specialLinearGroupEquivStatedSL 3 K
  let eSL' := specialLinearGroupEquivStatedSL 3 K'
  let θ' : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K') := π₁e.trans π₂e.symm
  let θSL : Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 3) K' :=
    eSL'.symm.toMonoidHom.comp (θ'.toMonoidHom.comp eSL.toMonoidHom)
  let ρ : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (Sec I' Z') :=
    (B5.secHom L hLI' hLZ').comp (π₁e.toMonoidHom.comp eSL.toMonoidHom)
  have hθSL : Function.Surjective θSL :=
    eSL'.symm.surjective.comp (θ'.surjective.comp eSL.surjective)
  have hπθ : ∀ g : ↥(StatedSL 3 K), π₂ (θ' g) = π₁e g := fun g => by
    change π₂e (π₂e.symm (π₁e g)) = π₁e g
    rw [MulEquiv.apply_symm_apply]
  have he := classification_he (π₁e := π₁e) (π₂ := π₂) (eSL := eSL)
    (θ' := θ') (ρ := ρ) (e₂ := e₂) hLI' hLZ' (fun g => rfl) hπθ he₂₀
  obtain ⟨dual, β, hβ, -⟩ :=
    CFSG.Quasithin.MS93.exists_natEquiv_or_dual_of_surj θSL hθSL ρ e₂ he
  exact secIsoL_of_classified (π₁e := π₁e) (e₁ := e₁) hKcard hRV₁.2.1 hRV₂.2.1 hAL
    hLI hLZ hLI' hLZ' he₁ (fun g => rfl) hAI hAZ hAI' hAZ' hfaith₁ hfaith₂ hA₁ hA₂
    hAnc hker hAel hcost dual β hβ

theorem gomiHomog_secIsoL_of_sl3 {W : Type} [CommGroup W] [Finite W]
    {L A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W} {a a' : ℕ}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (h₁ : BinaryNaturalSL L I Z 3 a) (h₂ : BinaryNaturalSL L I' Z' 3 a')
    (hA₁ : autSec A I Z ≤ autSec L I Z) (hA₂ : autSec A I' Z' ≤ autSec L I' Z')
    (hAnc : ¬ A ≤ centSec I Z) (hker : A ⊓ centSec I Z = A ⊓ centSec I' Z')
    (hAel : IsElemAbelian2 (autSec A I Z))
    (hcost : Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤ Nat.card ↥(autSec A I Z) *
      Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(fixV (autSec A I' Z'))) :
    SecIsoL L I Z I' Z' := by
  obtain ⟨K, hKf, hKfin, hKcard, π₁, hRV₁⟩ := h₁
  obtain ⟨K', hK'f, hK'fin, hK'card, π₂, hRV₂⟩ := h₂
  let := hKf
  let := hKfin
  let := hK'f
  let := hK'fin
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := a) (by rw [← Nat.card_eq_fintype_card, hKcard])
  have : CharP K' 2 := by
    have : Fintype K' := Fintype.ofFinite K'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := a') (by rw [← Nat.card_eq_fintype_card, hK'card])
  have h₁nat : IsGomiNatural L I Z :=
    isGomiNatural_of_binaryNaturalSL ⟨K, hKf, hKfin, hKcard, π₁, hRV₁⟩
  have h₂nat : IsGomiNatural L I' Z' :=
    isGomiNatural_of_binaryNaturalSL ⟨K', hK'f, hK'fin, hK'card, π₂, hRV₂⟩
  exact secIsoL_of_two_realizations hKcard hRV₁ hRV₂
    (IsGomiNatural.inf_centSec_eq_bot h₁nat) (IsGomiNatural.inf_centSec_eq_bot h₂nat)
    hAL hAI hAZ hAI' hAZ' hA₁ hA₂ hAnc hker hAel hcost

end CFSG.GroupTheory
