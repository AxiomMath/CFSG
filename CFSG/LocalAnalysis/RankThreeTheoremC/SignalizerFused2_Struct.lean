module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Pack
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerFused2_Refl
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.SectionRank.Ccomm
  Subgroup
open scoped commutatorElement

abbrev FusedQuot (p : ℕ) (H : Type*) [Group H] : Type _ := H ⧸ primeComplementCore (G := H) p

noncomputable abbrev fusedPi (p : ℕ) (H : Type*) [Group H] : H →* FusedQuot p H :=
  QuotientGroup.mk' (primeComplementCore (G := H) p)

structure FusedCentral (H : Type) [Group H] [Finite H] (p : ℕ) (P : Sylow p H) (z : H) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  order_z : orderOf z = p
  central : z ∈ Subgroup.center H
  mem_P : z ∈ (P : Subgroup H)
  layer : CFSG.layer (FusedQuot p H) = ⊥
  nongen : ∃ (Tbar : Sylow p (FusedQuot p H)) (X₀ : Subgroup (FusedQuot p H)),
    (Tbar : Subgroup (FusedQuot p H)) = (P : Subgroup H).map (fusedPi p H) ∧
      ReducedNongeneration p (FusedQuot p H) Tbar X₀

section Basic

variable {H : Type} [Group H] [Finite H] {p : ℕ} {P : Sylow p H}

theorem fusedInfBot (hp : p.Prime) (S : Subgroup H) (hS : IsPGroup p S) :
    S ⊓ primeComplementCore (G := H) p = ⊥ :=
  inf_eq_bot_of_isPGroup hp hS (primeComplementCore_coprime p)

theorem fusedPi_inj (hp : p.Prime) {S : Subgroup H} (hS : IsPGroup p S) {x y : H} (hx : x ∈ S)
    (hy : y ∈ S) (h : fusedPi p H x = fusedPi p H y) : x = y := by
  have hmem : x⁻¹ * y ∈ S ⊓ primeComplementCore (G := H) p :=
    ⟨S.mul_mem (S.inv_mem hx) hy, QuotientGroup.eq.mp h⟩
  rw [fusedInfBot hp S hS, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem

theorem card_map_fusedPi (hp : p.Prime) {S : Subgroup H} (hS : IsPGroup p S) :
    Nat.card (S.map (fusedPi p H)) = Nat.card S :=
  card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hS

end Basic

section XLevel

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime] {R : Sylow p X} {X₀ : Subgroup X} {z : X}
  {E C : Subgroup X} [E.Normal]
  {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}

theorem ReducedStructure3.zpowers_le_E (hrs : ReducedStructure3 p R X₀ z E C e) :
    zpowers z ≤ E := by
  rw [← hrs.center_eq]
  exact Subgroup.map_subtype_le _

omit [Fact p.Prime] in
theorem fusedPCore_le_sylow (R : Sylow p X) : CFSG.pCore p X ≤ (R : Subgroup X) := by
  have hQn : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  exact (CFSG.pCore_isPGroup (p := p) (G := X)).le_sylow_of_normal R

theorem ReducedStructure3.omega (hrs : ReducedStructure3 p R X₀ z E C e) {y : X}
    (hy : y ∈ CFSG.pCore p X) (hyp : y ^ p = 1) : y ∈ E := by
  rw [← hrs.sup_eq] at hy
  obtain ⟨g, hg, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  have hcomm : g * h = h * g := by
    have : h ∈ Subgroup.centralizer (E : Set X) := hrs.centralizer_eq ▸ hh
    exact Subgroup.mem_centralizer_iff.mp this g hg
  have hgp : g ^ p = 1 := hrs.pow_eq_one g hg
  rw [(show Commute g h from hcomm).mul_pow, hgp, one_mul] at hyp
  exact E.mul_mem hg (hrs.zpowers_le_E (hrs.omega_le h hh hyp))

theorem ReducedStructure3.exists_neg_one (hrs : ReducedStructure3 p R X₀ z E C e) :
    ∃ t : X, centerQuotientActionNormal E e t = -1 := by
  have hmem : (-1 : GL (Fin 2) (ZMod p)) ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 (ZMod p) := by
    rw [CFSG.RankThree.SubgroupLists.mem_statedSL_iff]
    simp [Matrix.det_neg]
  rw [← hrs.range_eq] at hmem
  exact hmem

theorem ReducedStructure3.commutator_mem_pCore (hrs : ReducedStructure3 p R X₀ z E C e) {t : X}
    (ht : centerQuotientActionNormal E e t = -1) (y : X) :
    t * y * t⁻¹ * y⁻¹ ∈ CFSG.pCore p X := by
  rw [← hrs.ker_eq, MonoidHom.mem_ker]
  have hc : ∀ M : GL (Fin 2) (ZMod p), (-1 : GL (Fin 2) (ZMod p)) * M = M * (-1) := fun M => by
    apply Units.ext
    simp [Units.val_neg]
  simp only [map_mul, map_inv, ht]
  rw [hc]
  simp

theorem ReducedStructure3.mul_conj_mem (hrs : ReducedStructure3 p R X₀ z E C e) {t : X}
    (ht : centerQuotientActionNormal E e t = -1) {u : X} (hu : u ∈ E) :
    u * (t * u * t⁻¹) ∈ zpowers z := by
  have hnegone : elemAutEquivGL e (autQuotient (Subgroup.center E) (MulAut.conjNormal (H := E) t))
      = -1 := ht
  have h1 := (elemAutEquivGL_eq_neg_one_iff e _).mp hnegone (QuotientGroup.mk ⟨u, hu⟩)
  rw [autQuotient_mk] at h1
  have h2 := QuotientGroup.eq.mp (h1.trans (QuotientGroup.mk_inv _ _))
  have h3 : (((MulAut.conjNormal (H := E) t ⟨u, hu⟩)⁻¹ * ⟨u, hu⟩⁻¹ : E) : X) ∈ zpowers z := by
    rw [← hrs.center_eq]
    exact ⟨_, h2, rfl⟩
  have h4 := inv_mem h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, mul_inv_rev,
    inv_inv] at h4
  exact h4

theorem ReducedStructure3.mem_pCore_iff (hrs : ReducedStructure3 p R X₀ z E C e) (x : X) :
    x ∈ CFSG.pCore p X ↔ ∀ u ∈ E, x * u * x⁻¹ * u⁻¹ ∈ zpowers z := by
  rw [← hrs.ker_eq]
  exact mem_ker_centerQuotientActionNormal hrs.center_eq e

theorem ReducedStructure3.le_E_of_plane [Finite X] (hrs : ReducedStructure3 p R X₀ z E C e)
    (hzp : orderOf z = p) {V : Subgroup X} (hVn : (R : Subgroup X) ≤ normalizer (V : Set X))
    (hVc : Nat.card V = p ^ 2) (hV1 : ∀ x ∈ V, x ^ p = 1)
    (hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hzV : z ∈ V) : V ≤ E := by
  by_cases h : ∀ y ∈ V ⊓ E, y ∈ zpowers z
  · intro x hx
    have hxQ : x ∈ CFSG.pCore p X := by
      rw [hrs.mem_pCore_iff]
      intro u hu
      have huR : u ∈ (R : Subgroup X) := fusedPCore_le_sylow R (hrs.le_pCore hu)
      have hE : x * u * x⁻¹ * u⁻¹ ∈ E :=
        E.mul_mem (Subgroup.Normal.conj_mem inferInstance u hu x) (E.inv_mem hu)
      have hV : x * u * x⁻¹ * u⁻¹ ∈ V := by
        have h1 : u * x⁻¹ * u⁻¹ ∈ V := (mem_normalizer_iff.mp (hVn huR) x⁻¹).mp (V.inv_mem hx)
        have := V.mul_mem hx h1
        rwa [show x * (u * x⁻¹ * u⁻¹) = x * u * x⁻¹ * u⁻¹ by group] at this
      exact h _ ⟨hV, hE⟩
    refine hrs.omega hxQ (hV1 x hx)
  · push Not at h
    obtain ⟨y, ⟨hyV, hyE⟩, hyz⟩ := h
    have hprime : p.Prime := Fact.out
    have hzp1 : z ^ p = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
    have hcard : Nat.card ↥(zpowers z ⊔ zpowers y) = p ^ 2 := by
      have hcomm : ∀ w ∈ zpowers z, w * y = y * w := fun w hw => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (Commute.zpow_left (show Commute z y from hVcomm z hzV y hyV) m).eq
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime (zpowers z) (hV1 y hyV) hyz hcomm,
        Nat.card_zpowers, hzp, pow_two]
    have hle : zpowers z ⊔ zpowers y ≤ V :=
      sup_le (Subgroup.zpowers_le.mpr hzV) (Subgroup.zpowers_le.mpr hyV)
    have heq : zpowers z ⊔ zpowers y = V :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hVc])
    rw [← heq]
    exact sup_le hrs.zpowers_le_E (Subgroup.zpowers_le.mpr hyE)

theorem ReducedStructure3.card_le_of_comm [Finite X]
    (hrs : ReducedStructure3 p R X₀ z E C e) {A : Subgroup X}
    (hAE : A ≤ E) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hdvd : Nat.card A ∣ p ^ 3 := by
    rw [← hrs.card_eq]
    exact Subgroup.card_dvd_of_le hAE
  obtain ⟨m, hm, hAm⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  by_cases h3 : m = 3
  · exfalso
    have hEA : A = E := Subgroup.eq_of_le_of_card_ge hAE (by rw [hAm, h3, hrs.card_eq])
    refine not_forall_mul_comm_of_mulEquiv e fun a b => ?_
    have := hA a (hEA ▸ a.2) b (hEA ▸ b.2)
    exact Subtype.ext this
  · rw [hAm]
    exact Nat.pow_le_pow_right hp.pos (by omega)

end XLevel

section HLevel

variable {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {P : Sylow p H} {z : H}

theorem FusedCentral.exists_structure (hF : FusedCentral H p P z) :
    ∃ (Tbar : Sylow p (FusedQuot p H)) (X₀ E C : Subgroup (FusedQuot p H)) (_ : E.Normal)
      (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)),
      (Tbar : Subgroup (FusedQuot p H)) = (P : Subgroup H).map (fusedPi p H) ∧
        ReducedStructure3 p Tbar X₀ (fusedPi p H z) E C e := by
  obtain ⟨Tbar, X₀, hT, hng⟩ := hF.nongen
  have hzc : fusedPi p H z ∈ Subgroup.center (FusedQuot p H) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := Subgroup.mem_center_iff.mp hF.central h
    show (QuotientGroup.mk h : FusedQuot p H) * (QuotientGroup.mk z) =
      QuotientGroup.mk z * QuotientGroup.mk h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
  have hzp : orderOf (fusedPi p H z) = p :=
    orderOf_mk_of_coprime hF.prime (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hF.order_z
  obtain ⟨E, C, hE, e, hrs⟩ := hng.exists_reducedStructure3 hF.layer hzc hzp
  exact ⟨Tbar, X₀, E, C, hE, e, hT, hrs⟩

variable {Tbar : Sylow p (FusedQuot p H)} {X₀ E C : Subgroup (FusedQuot p H)} [E.Normal]
  {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}

theorem FusedCentral.U_le_E (hF : FusedCentral H p P z)
    (hT : (Tbar : Subgroup (FusedQuot p H)) = (P : Subgroup H).map (fusedPi p H))
    (hrs : ReducedStructure3 p Tbar X₀ (fusedPi p H z) E C e) {U : Subgroup H}
    (hUP : U ≤ (P : Subgroup H)) (hUc : Nat.card U = p ^ 2) (hU1 : ∀ x ∈ U, x ^ p = 1)
    (hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hUN : ∀ x ∈ (P : Subgroup H), x ∈ normalizer (U : Set H)) (hzU : z ∈ U) :
    ∀ x ∈ U, fusedPi p H x ∈ E := by
  have hUp : IsPGroup p U := P.isPGroup'.to_le hUP
  have hzpo : orderOf (fusedPi p H z) = p :=
    orderOf_mk_of_coprime hF.prime (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hF.order_z
  have hVle : (U.map (fusedPi p H)) ≤ (Tbar : Subgroup (FusedQuot p H)) := by
    rw [hT]
    exact Subgroup.map_mono hUP
  have hVn : (Tbar : Subgroup (FusedQuot p H)) ≤
      normalizer ((U.map (fusedPi p H) : Subgroup (FusedQuot p H)) : Set (FusedQuot p H)) := by
    intro y hy
    rw [hT] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Subgroup.le_normalizer_map (fusedPi p H) ⟨x, hUN x hx, rfl⟩
  have hVc : Nat.card (U.map (fusedPi p H)) = p ^ 2 := by
    rw [card_map_fusedPi hF.prime hUp, hUc]
  have hV1 : ∀ x ∈ U.map (fusedPi p H), x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hU1 y hy, map_one]
  have hVcomm : ∀ x ∈ U.map (fusedPi p H), ∀ y ∈ U.map (fusedPi p H), x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hUcomm a ha b hb]
  have hle := hrs.le_E_of_plane hzpo hVn hVc hV1 hVcomm ⟨z, hzU, rfl⟩
  intro x hx
  exact hle ⟨x, hx, rfl⟩

theorem FusedCentral.exists_neg_one (hF : FusedCentral H p P z)
    (hT : (Tbar : Subgroup (FusedQuot p H)) = (P : Subgroup H).map (fusedPi p H))
    (hrs : ReducedStructure3 p Tbar X₀ (fusedPi p H z) E C e) :
    ∃ t : H, centerQuotientActionNormal E e (fusedPi p H t) = -1 ∧
      (∀ y ∈ (P : Subgroup H), t * y * t⁻¹ ∈ (P : Subgroup H)) ∧
        ∃ m : ℕ, ¬ p ∣ m ∧ t ^ m = 1 := by
  classical
  have hprime := hF.prime
  obtain ⟨tb, htb⟩ := hrs.exists_neg_one
  obtain ⟨t₁, rfl⟩ := QuotientGroup.mk_surjective tb
  change centerQuotientActionNormal E e (fusedPi p H t₁) = -1 at htb
  set π := fusedPi p H with hπ
  set Y : Subgroup H := (Tbar : Subgroup (FusedQuot p H)).comap π with hY
  have hPY : (P : Subgroup H) ≤ Y := fun x hx => by
    show π x ∈ (Tbar : Subgroup (FusedQuot p H))
    rw [hT]
    exact ⟨x, hx, rfl⟩
  have hcomm : ∀ y ∈ (P : Subgroup H),
      π (t₁ * y * t₁⁻¹) ∈ (Tbar : Subgroup (FusedQuot p H)) := by
    intro y hy
    have h1 := hrs.commutator_mem_pCore htb (π y)
    have h2 : π (t₁ * y * t₁⁻¹) = (π t₁ * π y * (π t₁)⁻¹ * (π y)⁻¹) * π y := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [h2]
    refine Tbar.mul_mem (fusedPCore_le_sylow Tbar h1) ?_
    rw [hT]
    exact ⟨y, hy, rfl⟩
  set P₂ : Subgroup H := (P : Subgroup H).map (MulAut.conj t₁).toMonoidHom with hP₂
  have hP₂Y : P₂ ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcomm y hy
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup H) Y :=
    ⟨P.subtype hPY, by rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPY]⟩
  have hP₂syl : CFSG.ABGLocalTools.IsSylowOf p P₂ Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hP₂Y ?_
    rw [hP₂, Subgroup.card_map_of_injective (MulAut.conj t₁).injective]
    exact hPsyl.card_eq
  obtain ⟨k, hkY, hkconj⟩ := hPsyl.exists_mem_conj hP₂syl
  have hkT : π k ∈ (Tbar : Subgroup (FusedQuot p H)) := hkY
  rw [hT] at hkT
  obtain ⟨x₀, hx₀, hx₀k⟩ := hkT
  set o₁ : H := k * x₀⁻¹ with ho₁
  have hπo₁ : π o₁ = 1 := by
    rw [ho₁, map_mul, map_inv, hx₀k]
    group
  have hpo : o₁ ∈ primeComplementCore (G := H) p := (QuotientGroup.eq_one_iff _).mp hπo₁
  have hconj : ∀ x : H, x ∈ P₂ ↔ o₁⁻¹ * x * o₁ ∈ (P : Subgroup H) := by
    intro x
    rw [hkconj x]
    have hk : k = o₁ * x₀ := by rw [ho₁]; group
    have h1 : k⁻¹ * x * k = x₀⁻¹ * (o₁⁻¹ * x * o₁) * x₀ := by rw [hk]; group
    rw [h1]
    constructor
    · intro h
      have := (P : Subgroup H).mul_mem ((P : Subgroup H).mul_mem hx₀ h)
        ((P : Subgroup H).inv_mem hx₀)
      simpa [mul_assoc] using this
    · intro h
      exact (P : Subgroup H).mul_mem ((P : Subgroup H).mul_mem ((P : Subgroup H).inv_mem hx₀) h)
        hx₀
  set t₂ : H := o₁⁻¹ * t₁ with ht₂
  have hnorm₂ : ∀ y ∈ (P : Subgroup H), t₂ * y * t₂⁻¹ ∈ (P : Subgroup H) := by
    intro y hy
    have h1 := (hconj (t₁ * y * t₁⁻¹)).mp ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rw [ht₂]
    convert h1 using 1
    group
  have hπt₂ : π t₂ = π t₁ := by
    rw [ht₂, map_mul, map_inv, hπo₁]
    group
  have hρt₂ : centerQuotientActionNormal E e (π t₂) = -1 := by rw [hπt₂]; exact htb
  obtain ⟨e', m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t₂).ne' p hprime.ne_one
  refine ⟨t₂ ^ (p ^ e'), ?_, ?_, m, hm, ?_⟩
  · rw [map_pow, map_pow, hρt₂]
    exact Odd.neg_one_pow ((hprime.odd_of_ne_two hF.odd).pow)
  · have hpow : ∀ n : ℕ, ∀ y ∈ (P : Subgroup H), t₂ ^ n * y * (t₂ ^ n)⁻¹ ∈ (P : Subgroup H) := by
      intro n
      induction n with
      | zero => intro y hy; simpa using hy
      | succ n ih =>
        intro y hy
        have := ih _ (hnorm₂ y hy)
        convert this using 1
        group
    exact hpow _
  · rw [← pow_mul, ← hord, pow_orderOf_eq_one]

theorem FusedCentral.exists_reflection (hF : FusedCentral H p P z)
    (hT : (Tbar : Subgroup (FusedQuot p H)) = (P : Subgroup H).map (fusedPi p H))
    (hrs : ReducedStructure3 p Tbar X₀ (fusedPi p H z) E C e) {U B : Subgroup H} {u : H}
    (hUP : U ≤ (P : Subgroup H)) (hUe : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2)
    (hUN : ∀ x ∈ (P : Subgroup H), x ∈ normalizer (U : Set H)) (hzU : z ∈ U) (huU : u ∈ U)
    (huz : u ∉ zpowers z)
    (hBdef : ∀ y : H, y ∈ B ↔ y ∈ (P : Subgroup H) ∧ y ^ p = 1 ∧ ∀ x ∈ U, y * x = x * y)
    (hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    ∃ (t : H) (c : ℤ), t * (u * z ^ c) * t⁻¹ = (u * z ^ c)⁻¹ ∧
      ∀ b ∈ B, ∃ i : ℤ, t * b * t⁻¹ = b * (u * z ^ c) ^ i := by
  classical
  have hprime := hF.prime
  have hodd := hF.odd
  set π := fusedPi p H with hπ
  have hzcen : ∀ g : H, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hF.central g
  have hz1 : z ≠ 1 := by
    intro h
    have := hF.order_z
    rw [h, orderOf_one] at this
    exact hprime.one_lt.ne this
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hU1 : ∀ x ∈ U, x ^ p = 1 := hUe.2
  have hUE := hF.U_le_E hT hrs hUP hUc hU1 hUcomm hUN hzU
  obtain ⟨t, hρt, htP, m, hm, htm⟩ := hF.exists_neg_one hT hrs
  have hconjU : ∀ x ∈ U, ∃ s : ℤ, x * (t * x * t⁻¹) = z ^ s := by
    intro x hx
    have hmem := hrs.mul_conj_mem hρt (hUE x hx)
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨s, ?_⟩
    have hxP : x ∈ (P : Subgroup H) := hUP hx
    have hmemP : x * (t * x * t⁻¹) ∈ (P : Subgroup H) :=
      (P : Subgroup H).mul_mem hxP (htP x hxP)
    have hzs : z ^ s ∈ (P : Subgroup H) := zpow_mem hF.mem_P s
    refine fusedPi_inj hprime P.isPGroup' hmemP hzs ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow]
    exact hs.symm
  obtain ⟨s, hs⟩ := hconjU u huU
  have hdiv2 : 2 ∣ p + 1 := by
    have := (hprime.odd_of_ne_two hodd).add_one
    exact even_iff_two_dvd.mp this
  set c : ℤ := -(s * (((p + 1) / 2 : ℕ) : ℤ)) with hc
  have hsc : (p : ℤ) ∣ s + 2 * c := by
    refine ⟨-s, ?_⟩
    have h2 : (2 : ℤ) * (((p + 1) / 2 : ℕ) : ℤ) = (p : ℤ) + 1 := by
      have := Nat.mul_div_cancel' hdiv2
      exact_mod_cast this
    rw [hc]
    linear_combination (-s) * h2
  have hzsc : z ^ (s + 2 * c) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hF.order_z]
    exact hsc
  set u₀ : H := u * z ^ c with hu₀
  have hu₀U : u₀ ∈ U := U.mul_mem huU (zpow_mem hzU c)
  have hu₀z : u₀ ∉ zpowers z := by
    intro h
    apply huz
    have : u = u₀ * (z ^ c)⁻¹ := by rw [hu₀]; group
    rw [this]
    exact (zpowers z).mul_mem h ((zpowers z).inv_mem (zpow_mem (Subgroup.mem_zpowers z) c))
  have hcentt : t * z * t⁻¹ = z := by rw [hzcen t]; group
  have huz' : u * z = z * u := hUcomm u huU z hzU
  have hinv : t * u₀ * t⁻¹ = u₀⁻¹ := by
    have h1 : t * u * t⁻¹ = u⁻¹ * z ^ s := by
      have : t * u * t⁻¹ = u⁻¹ * (u * (t * u * t⁻¹)) := by group
      rw [this, hs]
    have h2 : t * u₀ * t⁻¹ = (t * u * t⁻¹) * (t * z * t⁻¹) ^ c := by
      rw [hu₀, conj_zpow]; group
    rw [h2, h1, hcentt]
    have hcomm : u⁻¹ * z ^ s * z ^ c = u⁻¹ * z ^ (s + c) := by rw [mul_assoc, ← zpow_add]
    rw [hcomm, hu₀, mul_inv_rev]
    have h3 : z ^ (s + c) = (z ^ c)⁻¹ := by
      have : z ^ (s + c) * z ^ c = 1 := by rw [← zpow_add, show s + c + c = s + 2 * c by ring, hzsc]
      exact eq_inv_of_mul_eq_one_left this
    rw [h3]
    have : u⁻¹ * (z ^ c)⁻¹ = (z ^ c)⁻¹ * u⁻¹ :=
      (Commute.inv_inv ((Commute.zpow_left (show Commute z u from huz'.symm) c).symm)).eq
    rw [this]
  refine ⟨t, c, hinv, ?_⟩
  have htU : ∀ x ∈ U, t * x * t⁻¹ ∈ U := by
    intro x hx
    obtain ⟨s', hs'⟩ := hconjU x hx
    have h1 : t * x * t⁻¹ = x⁻¹ * z ^ s' := by
      have h : t * x * t⁻¹ = x⁻¹ * (x * (t * x * t⁻¹)) := by group
      rw [h, hs']
    rw [h1]
    exact U.mul_mem (U.inv_mem hx) (zpow_mem hzU s')
  have htpU : ∀ n : ℕ, ∀ x ∈ U, t ^ n * x * (t ^ n)⁻¹ ∈ U := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := ih _ (htU x hx)
      convert this using 1
      group
  have htinvU : ∀ x ∈ U, t⁻¹ * x * t ∈ U := by
    intro x hx
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm (dvd_zero p)
    have h1 := htpU (m - 1) x hx
    have hinv' : t ^ (m - 1) = t⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), htm]
    rw [hinv'] at h1
    simpa using h1
  have hBt : ∀ b ∈ B, t * b * t⁻¹ ∈ B := by
    intro b hb
    obtain ⟨hbP, hbp, hbU⟩ := (hBdef b).mp hb
    refine (hBdef _).mpr ⟨htP b hbP, ?_, ?_⟩
    · rw [conj_pow, hbp]
      group
    · intro x hx
      have h1 := hbU _ (htinvU x hx)
      calc t * b * t⁻¹ * x = t * (b * (t⁻¹ * x * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * x * t) * b) * t⁻¹ := by rw [h1]
        _ = x * (t * b * t⁻¹) := by group
  have hwU : ∀ b ∈ B, t * b * t⁻¹ * b⁻¹ ∈ U := by
    intro b hb
    have hwB : t * b * t⁻¹ * b⁻¹ ∈ B := B.mul_mem (hBt b hb) (B.inv_mem hb)
    obtain ⟨hwP, hwp, -⟩ := (hBdef _).mp hwB
    have hπw : π (t * b * t⁻¹ * b⁻¹) ∈ CFSG.pCore p (FusedQuot p H) := by
      have h1 := hrs.commutator_mem_pCore hρt (π b)
      have h2 : π (t * b * t⁻¹ * b⁻¹) = π t * π b * (π t)⁻¹ * (π b)⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [h2]
      exact h1
    have hπwp : (π (t * b * t⁻¹ * b⁻¹)) ^ p = 1 := by rw [← map_pow, hwp, map_one]
    have hwE : π (t * b * t⁻¹ * b⁻¹) ∈ E := hrs.omega hπw hπwp
    set Y : Subgroup H := B ⊓ E.comap π with hY
    have hYP : Y ≤ (P : Subgroup H) := fun y hy => ((hBdef y).mp hy.1).1
    have hUY : U ≤ Y := fun x hx =>
      ⟨(hBdef x).mpr ⟨hUP hx, hU1 x hx, fun x' hx' => hUcomm x hx x' hx'⟩, hUE x hx⟩
    have hYcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := fun x hx y hy => hBcomm x hx.1 y hy.1
    have hmapcomm : ∀ x ∈ Y.map π, ∀ y ∈ Y.map π, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b', hb', rfl⟩
      rw [← map_mul, ← map_mul, hYcomm a ha b' hb']
    have hle : Y.map π ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    have hcardY : Nat.card Y ≤ p ^ 2 := by
      have h1 := hrs.card_le_of_comm hle hmapcomm
      rwa [card_map_fusedPi hprime (P.isPGroup'.to_le hYP)] at h1
    have hUeqY : U = Y := Subgroup.eq_of_le_of_card_ge hUY (by rw [hUc]; exact hcardY)
    rw [hUeqY]
    exact ⟨hwB, hwE⟩
  intro b hb
  obtain ⟨hbP, hbp, hbU⟩ := (hBdef b).mp hb
  obtain ⟨i, j, hij⟩ := exists_pow_mul_pow_of_mem_plane hUe hUc hzU hz1 hu₀U hu₀z (hwU b hb)
  have hb_t : t * b * t⁻¹ = (u₀ ^ i * z ^ j) * b := by rw [← hij]; group
  have hu₀cz : u₀ * z = z * u₀ := hUcomm u₀ hu₀U z hzU
  have hzj_u : z ^ j * u₀ ^ i = u₀ ^ i * z ^ j :=
    (Commute.pow_pow (show Commute z u₀ from hu₀cz.symm) j i).eq
  have ht2 : t ^ 2 * b * (t ^ 2)⁻¹ = z ^ (2 * j) * b := by
    have e1 : t ^ 2 * b * (t ^ 2)⁻¹ = t * (t * b * t⁻¹) * t⁻¹ := by rw [pow_two]; group
    rw [e1, hb_t]
    have e2 : t * ((u₀ ^ i * z ^ j) * b) * t⁻¹ =
        (t * (u₀ ^ i * z ^ j) * t⁻¹) * (t * b * t⁻¹) := by group
    rw [e2, hb_t]
    have e3 : t * (u₀ ^ i * z ^ j) * t⁻¹ = (u₀⁻¹) ^ i * z ^ j := by
      have : t * (u₀ ^ i * z ^ j) * t⁻¹ = (t * u₀ * t⁻¹) ^ i * (t * z * t⁻¹) ^ j := by
        rw [conj_pow, conj_pow]
        group
      rw [this, hinv, hcentt]
    rw [e3]
    calc (u₀⁻¹) ^ i * z ^ j * (u₀ ^ i * z ^ j * b)
        = (u₀⁻¹) ^ i * (z ^ j * u₀ ^ i) * z ^ j * b := by simp only [mul_assoc]
      _ = (u₀⁻¹) ^ i * (u₀ ^ i * z ^ j) * z ^ j * b := by rw [hzj_u]
      _ = z ^ (2 * j) * b := by
        rw [two_mul, pow_add]
        simp only [← mul_assoc, inv_pow, inv_mul_cancel, one_mul]
  have hzcen' : ∀ n : ℕ, ∀ g : H, g * z ^ n = z ^ n * g := fun n g =>
    Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hF.central n) g
  have hind : ∀ n : ℕ, (t ^ 2) ^ n * b * ((t ^ 2) ^ n)⁻¹ = z ^ (2 * j * n) * b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : (t ^ 2) ^ (n + 1) * b * ((t ^ 2) ^ (n + 1))⁻¹ =
          (t ^ 2) ^ n * (t ^ 2 * b * (t ^ 2)⁻¹) * ((t ^ 2) ^ n)⁻¹ := by group
      rw [e1, ht2]
      have e2 : (t ^ 2) ^ n * (z ^ (2 * j) * b) * ((t ^ 2) ^ n)⁻¹ =
          ((t ^ 2) ^ n * z ^ (2 * j) * ((t ^ 2) ^ n)⁻¹) * ((t ^ 2) ^ n * b * ((t ^ 2) ^ n)⁻¹) := by
        group
      rw [e2, ih]
      have hzc : (t ^ 2) ^ n * z ^ (2 * j) * ((t ^ 2) ^ n)⁻¹ = z ^ (2 * j) := by
        rw [hzcen' (2 * j) ((t ^ 2) ^ n)]
        group
      rw [hzc, ← mul_assoc, ← pow_add]
      congr 2
      ring
  have htm2 : (t ^ 2) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, htm, one_pow]
  have hzjm : z ^ (2 * j * m) = 1 := by
    have := hind m
    rw [htm2] at this
    simp only [inv_one, mul_one, one_mul] at this
    have h1 : z ^ (2 * j * m) * b = 1 * b := by rw [one_mul]; exact this.symm
    exact mul_right_cancel h1
  have hpdvd : p ∣ 2 * j * m := by
    rw [← hF.order_z]
    exact orderOf_dvd_of_pow_eq_one hzjm
  have hp2 : ¬ p ∣ 2 := by
    intro h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp h)
  have hpj : p ∣ j := by
    rcases (Nat.Prime.dvd_mul hprime).mp hpdvd with h | h
    · rcases (Nat.Prime.dvd_mul hprime).mp h with h' | h'
      · exact absurd h' hp2
      · exact h'
    · exact absurd h hm
  have hzj : z ^ j = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hF.order_z]
    exact hpj
  refine ⟨(i : ℤ), ?_⟩
  rw [hb_t, hzj, mul_one, zpow_natCast]
  exact (Commute.pow_left (show Commute u₀ b from (hbU u₀ hu₀U).symm) i).eq

theorem FusedCentral.center_fixed (hF : FusedCentral H p P z) (θ : MulAut H) (k : ℤ)
    (hθz : θ z = z ^ k) {B' : Subgroup H} (hB'P : B' ≤ (P : Subgroup H))
    (hB'1 : ∀ x ∈ B', x ^ p = 1) (hB'comm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x)
    (hB'c : Nat.card B' = p ^ 3) (hθB : ∀ b ∈ B', ∃ i : ℤ, θ b = b * z ^ i) : z ^ k = z := by
  classical
  obtain ⟨Tbar, X₀, E, C, hE, e, hT, hrs⟩ := hF.exists_structure
  have hprime := hF.prime
  set π := fusedPi p H with hπ
  have hOchar : (primeComplementCore (G := H) p).Characteristic :=
    primeComplementCore_characteristic p
  set θb : MulAut (FusedQuot p H) := autQuotient (primeComplementCore (G := H) p) θ with hθb
  have hθbπ : ∀ x : H, θb (π x) = π (θ x) := fun x =>
    autQuotient_mk (primeComplementCore (G := H) p) θ x
  have hzo : orderOf (π z) = p :=
    orderOf_mk_of_coprime hprime (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hF.order_z
  have hπz : ∀ x ∈ zpowers (π z), ∃ m : ℤ, x = π (z ^ m) := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨m, by rw [map_zpow]⟩
  have hcomm : ∀ u v : E, ⁅u, v⁆ ∈ Subgroup.center E := fun u v => by
    have h := commutator_mem_center_of_mulEquiv e u v
    have h2 := Subgroup.mem_center_iff.mp h (u * v)
    have : ⁅u, v⁆ = (v * u)⁻¹ * (u * v) := by
      calc ⁅u, v⁆ = (u * v) * ((v * u)⁻¹ * (u * v)) * (u * v)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = (v * u)⁻¹ * (u * v) := by rw [h2]; group
    rw [this]
    exact h
  have hZ : Nat.card (Subgroup.center E) = p := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective, hrs.center_eq, Nat.card_zpowers, hzo]
  have hnc : ∃ a b : E, a * b ≠ b * a := by
    have := not_forall_mul_comm_of_mulEquiv e
    push Not at this
    exact this
  have hzmem : ∀ c : E, c ∈ Subgroup.center E ↔ (c : FusedQuot p H) ∈ zpowers (π z) := fun c => by
    rw [← hrs.center_eq]
    exact (Subgroup.mem_map_iff_mem E.subtype_injective).symm
  have hEchar : E.Characteristic := by
    rw [Subgroup.characteristic_iff_le_comap]
    intro φ x hx
    have h1 : φ x ∈ CFSG.pCore p (FusedQuot p H) := by
      rw [← pCore_map_iso p φ]
      exact ⟨x, hrs.le_pCore hx, rfl⟩
    refine hrs.omega h1 ?_
    rw [← map_pow, hrs.pow_eq_one x hx, map_one]
  set g : H →* FusedQuot p H ⧸ CFSG.pCore p (FusedQuot p H) :=
    (QuotientGroup.mk' (CFSG.pCore p (FusedQuot p H))).comp π with hg
  have hgker : ∀ x : H, x ∈ g.ker ↔ π x ∈ CFSG.pCore p (FusedQuot p H) := by
    intro x
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hcardmap : Nat.card (B'.map g) ≤ p := by
    have h1 : (CFSG.pCore p (FusedQuot p H)).relIndex (Tbar : Subgroup (FusedQuot p H)) = p :=
      hrs.relIndex_eq
    have h2 : Nat.card ((Tbar : Subgroup (FusedQuot p H)).map
        (QuotientGroup.mk' (CFSG.pCore p (FusedQuot p H)))) = p := by
      have h4 := Subgroup.relIndex_ker (K := (Tbar : Subgroup (FusedQuot p H)))
        (QuotientGroup.mk' (CFSG.pCore p (FusedQuot p H)))
      rw [QuotientGroup.ker_mk'] at h4
      rw [← h4]
      exact h1
    have h3 : B'.map g ≤ (Tbar : Subgroup (FusedQuot p H)).map
        (QuotientGroup.mk' (CFSG.pCore p (FusedQuot p H))) := by
      rw [hg, ← Subgroup.map_map]
      exact Subgroup.map_mono (show B'.map π ≤ Tbar by rw [hT]; exact Subgroup.map_mono hB'P)
    exact (Subgroup.card_le_of_le h3).trans h2.le
  have hmulcard : g.ker.relIndex B' * Nat.card (g.ker ⊓ B' : Subgroup H) = Nat.card B' :=
    Subgroup.relIndex_mul_card g.ker B'
  rw [Subgroup.relIndex_ker (K := B') g, hB'c] at hmulcard
  have hp2 : 2 ≤ p := hprime.two_le
  have hWcard : p ^ 2 ≤ Nat.card (g.ker ⊓ B' : Subgroup H) := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card (B'.map g) * Nat.card (g.ker ⊓ B' : Subgroup H) ≤
        p * Nat.card (g.ker ⊓ B' : Subgroup H) := Nat.mul_le_mul_right _ hcardmap
    have h2 : p * Nat.card (g.ker ⊓ B' : Subgroup H) < p * p ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hlt hprime.pos
    have h3 : p * p ^ 2 = p ^ 3 := by ring
    omega
  have hex_a : ∃ a ∈ B', π a ∈ CFSG.pCore p (FusedQuot p H) ∧ a ∉ zpowers z := by
    by_contra hnone
    push Not at hnone
    have hle : (g.ker ⊓ B' : Subgroup H) ≤ zpowers z := fun a ha =>
      hnone a ha.2 ((hgker a).mp ha.1)
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hF.order_z] at h1
    nlinarith [hWcard]
  have hex_b : ∃ b ∈ B', π b ∉ CFSG.pCore p (FusedQuot p H) := by
    by_contra hnone
    push Not at hnone
    have hle : B'.map π ≤ E := by
      rintro _ ⟨b, hb, rfl⟩
      refine hrs.omega (hnone b hb) ?_
      rw [← map_pow, hB'1 b hb, map_one]
    have hcm : ∀ x ∈ B'.map π, ∀ y ∈ B'.map π, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hB'comm a ha b hb]
    have h1 := hrs.card_le_of_comm hle hcm
    rw [card_map_fusedPi hprime (P.isPGroup'.to_le hB'P), hB'c] at h1
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hprime.one_lt (by norm_num)
    omega
  obtain ⟨a, haB, haQ, haz⟩ := hex_a
  obtain ⟨b₀, hb₀B, hb₀Q⟩ := hex_b
  have haE : π a ∈ E := by
    refine hrs.omega haQ ?_
    rw [← map_pow, hB'1 a haB, map_one]
  have hzcen : ∀ y : FusedQuot p H, y * π z = π z * y := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := Subgroup.mem_center_iff.mp hF.central h
    show (QuotientGroup.mk h : FusedQuot p H) * (QuotientGroup.mk z) =
      QuotientGroup.mk z * QuotientGroup.mk h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
  have hzcenz : ∀ (y : FusedQuot p H) (i : ℤ), y * (π z) ^ i = (π z) ^ i * y := fun y i =>
    (Commute.zpow_right (show Commute y (π z) from hzcen y) i).eq
  set σ : MulAut E := MulAut.characteristic E θb with hσdef
  set τ : MulAut E := MulAut.conjNormal (H := E) (π b₀) with hτdef
  have hσ : ∀ c ∈ Subgroup.center E, σ c = c ^ k := by
    intro c hc
    obtain ⟨m, hm⟩ := hπz _ ((hzmem c).mp hc)
    apply Subtype.ext
    show θb (c : FusedQuot p H) = (c : FusedQuot p H) ^ k
    rw [hm, hθbπ, map_zpow θ z m, hθz, ← map_zpow, ← zpow_mul, ← zpow_mul, mul_comm]
  have hστ : σ * τ = τ * σ := by
    ext w
    obtain ⟨i, hi⟩ := hθB b₀ hb₀B
    show θb ((π b₀) * (w : FusedQuot p H) * (π b₀)⁻¹) =
      (π b₀) * θb (w : FusedQuot p H) * (π b₀)⁻¹
    have h1 : θb (π b₀) = π b₀ * (π z) ^ i := by
      rw [hθbπ, hi, map_mul, map_zpow]
    rw [map_mul, map_mul, map_inv, h1]
    calc π b₀ * (π z) ^ i * θb (w : FusedQuot p H) * (π b₀ * (π z) ^ i)⁻¹
        = π b₀ * ((π z) ^ i * θb (w : FusedQuot p H)) * (π z) ^ (-i) * (π b₀)⁻¹ := by group
      _ = π b₀ * (θb (w : FusedQuot p H) * (π z) ^ i) * (π z) ^ (-i) * (π b₀)⁻¹ := by
        rw [← hzcenz (θb (w : FusedQuot p H)) i]
      _ = π b₀ * θb (w : FusedQuot p H) * (π b₀)⁻¹ := by group
  have hτp : τ ^ p = 1 := by
    have h1 : (π b₀) ^ p = 1 := by rw [← map_pow, hB'1 b₀ hb₀B, map_one]
    rw [hτdef, ← map_pow, h1, map_one]
  have hτ1 : ¬ ∀ x : E, x⁻¹ * τ x ∈ Subgroup.center E := by
    intro hall
    apply hb₀Q
    rw [hrs.mem_pCore_iff]
    intro u hu
    have h1 := (hzmem _).mp (hall ⟨u, hu⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτdef, MulAut.conjNormal_apply] at h1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : π b₀ * u * (π b₀)⁻¹ * u⁻¹ = (π z) ^ m := by
      calc π b₀ * u * (π b₀)⁻¹ * u⁻¹ = u * (u⁻¹ * (π b₀ * u * (π b₀)⁻¹)) * u⁻¹ := by group
        _ = u * (π z) ^ m * u⁻¹ := by rw [hm]
        _ = (π z) ^ m := by rw [hzcenz u m]; group
    rw [h2]
    exact Subgroup.zpow_mem_zpowers _ m
  have haz' : (⟨π a, haE⟩ : E) ∉ Subgroup.center E := by
    intro hc
    obtain ⟨m, hm⟩ := hπz _ ((hzmem _).mp hc)
    apply haz
    have : a = z ^ m := fusedPi_inj hprime P.isPGroup' (hB'P haB) (zpow_mem hF.mem_P m) hm
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ m
  have hτa : τ ⟨π a, haE⟩ = ⟨π a, haE⟩ := by
    apply Subtype.ext
    show π b₀ * π a * (π b₀)⁻¹ = π a
    rw [← map_inv, ← map_mul, ← map_mul, show b₀ * a * b₀⁻¹ = a by
      rw [hB'comm b₀ hb₀B a haB]; group]
  have hσa : ∃ c ∈ Subgroup.center E, σ ⟨π a, haE⟩ = ⟨π a, haE⟩ * c := by
    obtain ⟨i, hi⟩ := hθB a haB
    have hcE : (π z) ^ i ∈ E := zpow_mem (hrs.zpowers_le_E (Subgroup.mem_zpowers _)) i
    refine ⟨⟨(π z) ^ i, hcE⟩, (hzmem _).mpr (Subgroup.zpow_mem_zpowers _ i), ?_⟩
    apply Subtype.ext
    show θb (π a) = π a * (π z) ^ i
    rw [hθbπ, hi, map_mul, map_zpow]
  have hk := reflection_center_fixed_aut hcomm hZ hnc e σ τ k hσ hστ hτp hτ1 haz' hτa hσa
  have hk1 : ((k - 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hk]
    ring
  have hdvd : (p : ℤ) ∣ k - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hk1
  have hz1 : z ^ (k - 1) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hF.order_z]
    exact hdvd
  calc z ^ k = z ^ (k - 1) * z := by rw [← _root_.zpow_add_one]; congr 1; ring
    _ = z := by rw [hz1, one_mul]

end HLevel

end CFSG.LocalAnalysis.RankThreeTheoremC
