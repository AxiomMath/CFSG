module

public import CFSG.CGT.PushingUpLit.T2KSW.FieldAutSylow
public import CFSG.CGT.PushingUpLit.LIT.A4.Leaves
import CFSG.CGT.PushingUpLit.T2KSW.FieldAutCount
import CFSG.CGT.PushingUpLit.LIT.A4.T211Proof

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KR
open scoped commutatorElement
open Aux

namespace Har

variable {G : Type} [Group G] [Finite G]

theorem exists_index_two {M T : Subgroup G} (hT : IsSylowOf 2 T M) {Γ : Type} [Group Γ] [Finite Γ]
    [IsCyclic Γ] (f : ↥M →* Γ) (hf : ∃ x : ↥M, (x : G) ∈ T ∧ f x ≠ 1) :
    ∃ M₁ : Subgroup G, M₁ ≤ M ∧ M₁.relIndex M = 2 ∧ (∀ m ∈ M, ∀ y ∈ M₁, m * y * m⁻¹ ∈ M₁) ∧
      (∀ y : ↥M, f y = 1 → (y : G) ∈ M₁) ∧ ¬ T ≤ M₁ := by
  classical
  obtain ⟨x, hxT, hx1⟩ := hf
  set N : ℕ := Nat.card f.range with hN
  have hNpos : 0 < N := Nat.card_pos
  have hNeven : 2 ∣ N := by
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨(x : G), hxT⟩
    have hk' : x ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hfx : (f x) ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    have h1 : orderOf (f x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hfx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      exact hx1 (orderOf_eq_one_iff.1 hj)
    have h2 : orderOf (f x) ∣ N := by
      let a : ↥f.range := ⟨f x, f.mem_range.2 ⟨x, rfl⟩⟩
      have h3 : orderOf a ∣ N := orderOf_dvd_natCard a
      rwa [← Subgroup.orderOf_coe a] at h3
    exact (show 2 ∣ orderOf (f x) by rw [hj]; exact dvd_pow_self 2 hj0).trans h2
  have hN2 : 0 < N / 2 := by
    obtain ⟨c, hc⟩ := hNeven
    have : 2 ≤ N := by
      by_contra h2
      omega
    omega
  have hcomm : ∀ a b : Γ, a * b = b * a := fun a b =>
    (inferInstance : IsMulCommutative Γ).is_comm.comm a b
  let p : ↥M →* Γ := MonoidHom.mk' (fun y => (f y) ^ (N / 2)) fun a b => by
    rw [map_mul]
    exact Commute.mul_pow (hcomm _ _) _
  have hp : ∀ y, p y = (f y) ^ (N / 2) := fun y => rfl
  have hrel2 : (p.ker.map M.subtype).relIndex M = 2 := by
    have hsub : ((p.ker.map M.subtype).subgroupOf M) = p.ker := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hidx : (p.ker.map M.subtype).relIndex M = Nat.card p.range := by
      rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
    rw [hidx]
    have hle : Nat.card p.range ≤ 2 := by
      have : Fintype Γ := Fintype.ofFinite _
      have hcard : Nat.card {a : Γ // a ^ 2 = 1} ≤ 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact IsCyclic.card_pow_eq_one_le (α := Γ) (by norm_num)
      have hmem : ∀ a : p.range, a.1 ^ 2 = 1 := by
        rintro ⟨a, y, hy⟩
        show a ^ 2 = 1
        have h1 : (⟨f y, f.mem_range.2 ⟨y, rfl⟩⟩ : f.range) ^ N = 1 := pow_card_eq_one'
        have h2 : (f y) ^ N = 1 := by simpa using congrArg Subtype.val h1
        obtain ⟨c, hc⟩ := hNeven
        rw [← hy, hp, ← pow_mul]
        have : N / 2 * 2 = N := by omega
        rw [this, h2]
      exact (Nat.card_le_card_of_injective
        (fun a : p.range => (⟨a.1, hmem a⟩ : {a : Γ // a ^ 2 = 1}))
        (fun a b h => by
          have := congrArg Subtype.val h
          exact Subtype.ext this)).trans hcard
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥f.range)
    obtain ⟨x₀, hx₀⟩ := γ.2
    have hord : orderOf (f x₀) = N := by
      rw [hx₀, Subgroup.orderOf_coe]
      exact hγ
    have hpx₀ : p x₀ ≠ 1 := by
      intro h1
      rw [hp] at h1
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      have := Nat.le_of_dvd hN2 h2
      omega
    have hne : Nat.card p.range ≠ 1 := by
      intro h1
      have := Subgroup.card_eq_one.1 h1
      exact hpx₀ (by
        have hm : p x₀ ∈ p.range := ⟨x₀, rfl⟩
        rw [this, Subgroup.mem_bot] at hm
        exact hm)
    have hpos : 0 < Nat.card p.range := Nat.card_pos
    omega
  refine ⟨p.ker.map M.subtype, Subgroup.map_subtype_le _, hrel2, fun m hm y hy => ?_,
    fun y hy => ?_, ?_⟩
  · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨⟨m, hm⟩ * y' * ⟨m, hm⟩⁻¹, ?_, by simp⟩
    rw [MonoidHom.mem_ker] at hy' ⊢
    rw [map_mul, map_mul, hy', mul_one, map_inv, mul_inv_cancel]
  · refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    rw [MonoidHom.mem_ker, hp, hy, one_pow]
  · intro hTM₁
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 := Subgroup.relIndex_mul_relIndex T (p.ker.map M.subtype) M hTM₁
      (Subgroup.map_subtype_le _)
    have h2 : ¬ 2 ∣ T.relIndex M := (isSylowOf_iff.1 hT).2.2
    apply h2
    rw [← h1, hrel2]
    exact Dvd.intro_left _ rfl


@[expose] noncomputable def toGalHom (n : ℕ) :
    (GaloisField 2 n ≃+* GaloisField 2 n) →*
      (GaloisField 2 n ≃ₐ[ZMod 2] GaloisField 2 n) where
  toFun := toGal n
  map_one' := toGal_one n
  map_mul' := toGal_mul n

variable {L M T : Subgroup G} {n : ℕ}

theorem centralizer_le_M_of_Ec (hs : Sec4 G L M T n) {x : G} (hx : x ∈ Ec L T) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  have hsq : x ^ 2 = 1 := hs.S_elem.2 x hx
  obtain ⟨N, hCN, hNmax⟩ :=
    RankThree.PartOne.Sec15Final.exists_isMaximalTwoLocal_ge (isPLocal_centralizer_of_sq hsq hx1)
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hx.2 l hl)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun y hy => hCN (hLC hy)⟩
    rw [hs.hyp.unique] at this
    exact this
  rw [← hNM]
  exact hCN

theorem noTwoQuotient_of_sec4 (hs : Sec4 G L M T n) : A4.NoTwoQuotient G := by
  intro N hN hq
  rcases hs.hyp.simple.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have hL : IsPGroup 2 G := by
      have h1 : Nat.card (G ⧸ N) = Nat.card G := by
        rw [← Subgroup.index_eq_card, h, Subgroup.index_bot]
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hq
      exact (IsPGroup.iff_card (p := 2)).2 ⟨k, by rw [← h1, hk]⟩
    exact hs.hyp.natBlock.not_isPGroup (hL.of_injective L.subtype Subtype.coe_injective)
  · exact h

theorem false_of_transfer (hs : Sec4 G L M T n) {A : Subgroup G} (hA : IsFamily L T A)
    (hCNT : Syl.LemmaCNT L T A) {M₁ : Subgroup G}
    (hM₁N : ∀ m ∈ M, ∀ y ∈ M₁, m * y * m⁻¹ ∈ M₁) (hT₁M₁ : Rl L T ⊔ Dc L T ≤ M₁) {g : G}
    (hidx : M.relIndex (A.map (MulAut.conj g).toMonoidHom) ≤ 2)
    (hnot : ¬ (A.map (MulAut.conj g).toMonoidHom ⊓ M ≤ M₁)) : False := by
  have hAT : A ≤ T := hA.le_Dc.trans Dc_le_T
  set A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom with hA'
  set C : Subgroup G := A' ⊓ M with hC
  have hA'2 : IsPGroup 2 ↥A' := (hs.sylow.isPGroup.to_le hAT).map _
  have hCM : C ≤ M := inf_le_right
  have hC2 : IsPGroup 2 ↥C := hA'2.to_le inf_le_left
  obtain ⟨m, hmM, hmT⟩ := exists_conj_le_of_isPGroup hs.sylow hC2 hCM
  set B : Subgroup G := C.map (MulAut.conj m).toMonoidHom with hB
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hA.comm a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * a * m⁻¹ * (m * b * m⁻¹) = m * (a * b) * m⁻¹ := by group
      _ = m * (b * a) * m⁻¹ := by rw [hA'comm a ha.1 b hb.1]
      _ = m * b * m⁻¹ * (m * a * m⁻¹) := by group
  have hBnot : ¬ B ≤ Rl L T ⊔ Dc L T := by
    intro hBle
    apply hnot
    intro c hc
    have hmc : m * c * m⁻¹ ∈ B := ⟨c, hc, by simp [MulAut.conj_apply]⟩
    have h1 := hM₁N m⁻¹ (M.inv_mem hmM) _ (hT₁M₁ (hBle hmc))
    simpa [mul_assoc] using h1
  have hrel := Subgroup.relIndex_mul_card (H := M) (K := A')
  rw [inf_comm] at hrel
  have hcardA' : Nat.card A' = Nat.card A := card_map_conj A g
  have hBc : Nat.card B = Nat.card C := card_map_conj C m
  have hAB : Nat.card A ≤ 2 * Nat.card B := by
    rw [← hcardA', ← hrel, hBc]
    exact Nat.mul_le_mul_right _ hidx
  obtain ⟨hcnt1, hcnt2⟩ := hCNT B hmT hBcomm hBnot
  by_cases hE : B ⊓ Ec L T = ⊥
  · have := hcnt2 hE
    omega
  · obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    set A'' : Subgroup G := A.map (MulAut.conj (m * g)).toMonoidHom with hA''
    have hBA'' : B ≤ A'' := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hc.1
      exact ⟨a, ha, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hA''comm : ∀ a ∈ A'', ∀ b ∈ A'', a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc m * g * a * (m * g)⁻¹ * (m * g * b * (m * g)⁻¹)
          = (m * g) * (a * b) * (m * g)⁻¹ := by group
        _ = (m * g) * (b * a) * (m * g)⁻¹ := by rw [hA.comm a ha b hb]
        _ = m * g * b * (m * g)⁻¹ * (m * g * a * (m * g)⁻¹) := by group
    have hA''M : A'' ≤ M := by
      intro y hy
      apply centralizer_le_M_of_Ec hs he.2 he1'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hA''comm y hy e (hBA'' he.1)
    have hA''B : A'' ≤ B := by
      rintro _ ⟨a, ha, rfl⟩
      have hyM : (MulAut.conj (m * g)).toMonoidHom a ∈ M := hA''M ⟨a, ha, rfl⟩
      refine ⟨g * a * g⁻¹, ⟨⟨a, ha, rfl⟩, ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hyM' : m * (g * a * g⁻¹) * m⁻¹ ∈ M := by
        have e0 : (MulAut.conj (m * g)).toMonoidHom a = m * (g * a * g⁻¹) * m⁻¹ := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [← e0]
        exact hyM
      have h1 : m⁻¹ * (m * (g * a * g⁻¹) * m⁻¹) * m ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem hmM) hyM') hmM
      have e1 : m⁻¹ * (m * (g * a * g⁻¹) * m⁻¹) * m = g * a * g⁻¹ := by group
      rwa [e1] at h1
    have hcardA'' : Nat.card A'' = Nat.card A := card_map_conj A (m * g)
    have := Subgroup.card_le_of_le hA''B
    omega


end Har

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

open Har

theorem t_le_rd_of_cnt (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hA78 : Aschbacher78OneGen) (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) {A : Subgroup G}
    (hA : IsMaximalFamily L T A) (hCNT : Syl.LemmaCNT L T A) : T ≤ Rl L T ⊔ Dc L T := by
  by_contra hTT
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  have hT : IsSylowOf 2 T M := hs.sylow
  let H : CoordData G L M n := ⟨h.natData, h, hLM, hMN⟩
  let f : ↥M →* (GaloisField 2 n ≃ₐ[ZMod 2] GaloisField 2 n) :=
    (toGalHom n).comp (WeakCl.chi H)
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hT.le)
  have hfT1 : ∀ y : ↥M, (y : G) ∈ Rl L T ⊔ Dc L T → f y = 1 := by
    intro y hy
    obtain ⟨r, hr, d, hd, hyrd⟩ := (mem_sup_iff_mul hRn).1 hy
    have hr1 : WeakCl.chi H ⟨r, hLM hr.2⟩ = 1 := WeakCl.chi_of_mem_L H hr.2
    have hdc : d ∈ cenW L M := by
      have := hd
      rw [Dc_eq_inf_cenW h hMN hT] at this
      exact this.2
    have hd1 : WeakCl.chi H ⟨d, hT.le hd.1⟩ = 1 := WeakCl.chi_of_mem_cenW H hdc
    have hy' : y = ⟨r, hLM hr.2⟩ * ⟨d, hT.le hd.1⟩ := Subtype.ext hyrd
    rw [MonoidHom.comp_apply, hy', map_mul, hr1, hd1, mul_one, map_one]
  have hf : ∃ x : ↥M, (x : G) ∈ T ∧ f x ≠ 1 := by
    obtain ⟨x, hxT, hxn⟩ := Set.not_subset.1 hTT
    refine ⟨⟨x, hT.le hxT⟩, hxT, fun h1 => hxn ?_⟩
    have hchi : WeakCl.chi H ⟨x, hT.le hxT⟩ = 1 := by
      apply toGal_injective n
      have := h1
      rw [MonoidHom.comp_apply] at this
      rw [toGal_one n]
      exact this
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨x, hxT⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hK := WeakCl.mem_K_of_chi_eq_one H (hT.le hxT) hk' hchi
    rw [← inf_sup_cenW h hLM hMN hT]
    exact ⟨hxT, hK⟩
  obtain ⟨M₁, hM₁M, hrel2, hM₁N, hker, -⟩ := exists_index_two hT f hf
  have hT₁M₁ : Rl L T ⊔ Dc L T ≤ M₁ := fun y hy =>
    hker ⟨y, hT.le (sup_le Rl_le_T Dc_le_T hy)⟩ (hfT1 _ hy)
  have hAT : A ≤ T := hA.1.le_Dc.trans Dc_le_T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, hidx, hnot⟩ := A4.haradaTransfer211 G (noTwoQuotient_of_sec4 hs) M M₁ T A hM₁M
    hrel2 hT.le hT.isPGroup ((isSylowOf_iff.1 hT).2.2) hAT
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hAT).2 hA.1.normal) hA.1.comm
    (fun a ha => family_pow_four_eq_one hs hE1 hA.1 ha) (family_normalizer_le hs hE1 hA.1)
    (fun g hg => Syl.sylow_type hs hE1 hA78 hWVE hA hCNT hg)
  exact false_of_transfer hs hA.1 hCNT hM₁N hT₁M₁ hidx hnot

theorem t_le_rd (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) (hA78 : Aschbacher78OneGen)
    (hE : Ec L T ≠ ⊥) (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) : T ≤ Rl L T ⊔ Dc L T := by
  obtain ⟨A, hA⟩ := exists_isMaximalFamily hs hE1
  exact t_le_rd_of_cnt hs hE1 hA78 hWVE hA (cnt_of_maximal hs hE1 hE hA)


end CFSG.CGT.PushingUpLit.T2KSW
