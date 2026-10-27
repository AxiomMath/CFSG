module

public import CFSG.CGT.Stroth77.Section1Module
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)
open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator

variable {G : Type} [Group G] [Finite G] {E : Subgroup G}

theorem mul_comm_of_isE {n : ℕ} (hE : IsE n ↥E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := by
  have h := hE.1.1.is_comm.comm ⟨⟨x, hx⟩, trivial⟩ ⟨⟨y, hy⟩, trivial⟩
  exact congrArg (fun z : (⊤ : Subgroup ↥E) => ((z : ↥E) : G)) h

theorem mul_self_of_isE {n : ℕ} (hE : IsE n ↥E) {x : G} (hx : x ∈ E) : x * x = 1 := by
  have h := hE.1.2 ⟨x, hx⟩ trivial
  rw [← pow_two]
  exact congrArg Subtype.val h

theorem isPGroup_of_isE {n : ℕ} (hE : IsE n ↥E) : IsPGroup 2 E :=
  IsPGroup.of_card hE.2

theorem centralizer_le_normalizer_set : Subgroup.centralizer (E : Set G) ≤
    Subgroup.normalizer (E : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro e
  rw [Subgroup.mem_centralizer_iff] at hc
  constructor
  · intro he
    rw [← hc e he, mul_inv_cancel_right]
    exact he
  · intro he
    have h := hc
    by_contra hne
    apply hne
    have hce : c * e * c⁻¹ ∈ E := he
    have hc' : ∀ x ∈ E, c⁻¹ * x = x * c⁻¹ := by
      intro x hx
      have := h x hx
      calc c⁻¹ * x = c⁻¹ * x * c * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [mul_assoc c⁻¹ x c, ← this]
        _ = x * c⁻¹ := by group
    have := hc' _ hce
    have e1 : e = c⁻¹ * (c * e * c⁻¹) * c := by group
    rw [e1, this]
    convert hce using 1
    group

theorem exists_odd_complement_centralizer (hE : IsE 4 ↥E)
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E) :
    ∃ K : Subgroup G, K ≤ Subgroup.centralizer (E : Set G) ∧ Odd (Nat.card K) ∧
      (∀ c : G, c ∈ K ↔ c ∈ Subgroup.centralizer (E : Set G) ∧ Odd (orderOf c)) ∧
      (∀ c ∈ Subgroup.centralizer (E : Set G), ∃ e ∈ E, ∃ k ∈ K, c = e * k) ∧
      Subgroup.centralizer (E : Set G) = E ⊔ K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (E : Set G) with hC
  have hEC : E ≤ C := hsyl.1
  have hP2 : IsPGroup 2 (E.subgroupOf C) :=
    (isPGroup_of_isE hE).comap_of_injective C.subtype Subtype.val_injective
  have hidx : ¬ 2 ∣ (E.subgroupOf C).index := hsyl.2.2
  set P : Sylow 2 ↥C := hP2.toSylow hidx with hPdef
  have hPcoe : (P : Subgroup ↥C) = E.subgroupOf C := IsPGroup.toSylow_coe hP2 hidx
  have hcentral : ∀ (c : ↥C) (p : ↥C), (p : G) ∈ E → c * p = p * c := by
    intro c p hp
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2 p hp).symm
  have hPnc : Subgroup.normalizer (P : Set ↥C) ≤ Subgroup.centralizer (P : Set ↥C) := by
    intro c _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ (P : Subgroup ↥C) := hp
    rw [hPcoe] at hp'
    exact (hcentral c p (Subgroup.mem_subgroupOf.mp hp')).symm
  set K' := (MonoidHom.transferSylow P hPnc).ker with hK'
  have hcompl : Subgroup.IsComplement' K' P := MonoidHom.ker_transferSylow_isComplement' P hPnc
  have hK'odd : Odd (Nat.card K') := by
    have := MonoidHom.not_dvd_card_ker_transferSylow P hPnc
    rw [← hK'] at this
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp this)
  set K : Subgroup G := K'.map C.subtype with hKdef
  have hKcard : Nat.card K = Nat.card K' :=
    Subgroup.card_map_of_injective Subtype.val_injective
  have hKC : K ≤ C := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hdecomp : ∀ c : ↥C, ∃ k ∈ K', ∃ p ∈ (P : Subgroup ↥C), k * p = c := by
    intro c
    obtain ⟨⟨k, p⟩, hkp, -⟩ := Subgroup.IsComplement.existsUnique hcompl c
    exact ⟨k, k.2, p, p.2, hkp⟩
  have hdisj : Disjoint K' (P : Subgroup ↥C) := hcompl.disjoint
  have hdecG : ∀ c ∈ C, ∃ e ∈ E, ∃ k ∈ K, c = e * k := by
    intro c hc
    obtain ⟨k, hk, p, hp, hkp⟩ := hdecomp ⟨c, hc⟩
    rw [hPcoe] at hp
    have hpE : (p : G) ∈ E := Subgroup.mem_subgroupOf.mp hp
    refine ⟨p, hpE, k, ⟨k, hk, rfl⟩, ?_⟩
    have h1 := congrArg Subtype.val hkp
    simp only [Subgroup.coe_mul] at h1
    rw [← h1]
    exact (Subgroup.mem_centralizer_iff.mp k.2 p hpE).symm
  refine ⟨K, hKC, hKcard ▸ hK'odd, fun c => ⟨?_, ?_⟩, hdecG, ?_⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    have hdvd : orderOf (⟨k, hk⟩ : K') ∣ Nat.card K' := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hK'odd hdvd
  · rintro ⟨hc, hodd⟩
    obtain ⟨k, hk, p, hp, hkp⟩ := hdecomp ⟨c, hc⟩
    rw [hPcoe] at hp
    have hpE : (p : G) ∈ E := Subgroup.mem_subgroupOf.mp hp
    have hcomm : Commute k p := hcentral k p hpE
    set m := orderOf c with hm
    have hcm : (⟨c, hc⟩ : ↥C) ^ m = 1 := by
      apply Subtype.ext
      simp [hm, pow_orderOf_eq_one]
    rw [← hkp, hcomm.mul_pow] at hcm
    have hpm : p ^ m ∈ K' := by
      have : p ^ m = (k ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hcm
      rw [this]
      exact K'.inv_mem (K'.pow_mem hk m)
    have hpmP : p ^ m ∈ (P : Subgroup ↥C) := (P : Subgroup ↥C).pow_mem (hPcoe ▸ hp) m
    have hpm1 : p ^ m = 1 := Subgroup.disjoint_def.mp hdisj hpm hpmP
    have hp2 : p * p = 1 := by
      apply Subtype.ext
      exact mul_self_of_isE hE hpE
    have hp1 : p = 1 := by
      obtain ⟨r, hr⟩ := hodd
      rw [hr, pow_succ, pow_mul, sq, hp2, one_pow, one_mul] at hpm1
      exact hpm1
    rw [hp1, mul_one] at hkp
    exact ⟨k, hk, by rw [hkp]; rfl⟩
  · apply le_antisymm
    · intro c hc
      obtain ⟨e, he, k, hk, rfl⟩ := hdecG c hc
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hk)
    · exact sup_le hEC hKC

theorem oddCore_normalizer_eq (hE : IsE 4 ↥E) {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer (E : Set G)) (hKodd : Odd (Nat.card K))
    (hKiff : ∀ c : G, c ∈ K ↔ c ∈ Subgroup.centralizer (E : Set G) ∧ Odd (orderOf c)) :
    CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)) =
      K.subgroupOf (Subgroup.normalizer (E : Set G)) := by
  set N := Subgroup.normalizer (E : Set G) with hN
  have hKN : K ≤ N := hKC.trans centralizer_le_normalizer_set
  apply le_antisymm
  · refine sSup_le fun M hM => ?_
    obtain ⟨hMn, hModd⟩ := hM
    intro m hm
    rw [Subgroup.mem_subgroupOf, hKiff]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      set e' : ↥N := ⟨e, Subgroup.le_normalizer he⟩ with he'
      have hx : m * e' * m⁻¹ * e'⁻¹ ∈ M := by
        have := hMn.conj_mem _ (M.inv_mem hm) e'
        have h2 := M.mul_mem hm this
        convert h2 using 1
        group
      have hxE : ((m * e' * m⁻¹ * e'⁻¹ : ↥N) : G) ∈ E := by
        have hme : (m : G) * e * (m : G)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp m.2 e).mp he
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact E.mul_mem hme (E.inv_mem he)
      have hx1 : m * e' * m⁻¹ * e'⁻¹ = 1 := by
        set x := m * e' * m⁻¹ * e'⁻¹ with hxdef
        have hdvd : orderOf x ∣ Nat.card M := by
          have := orderOf_dvd_natCard (⟨x, hx⟩ : M)
          rwa [Subgroup.orderOf_mk] at this
        have hx2 : x ^ 2 = 1 := by
          apply Subtype.ext
          rw [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
          exact mul_self_of_isE hE hxE
        have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
        have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hModd hdvd
        have h1 : orderOf x = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
          · exact h
          · rw [h] at hodd'; exact absurd hodd' (by decide)
        exact orderOf_eq_one_iff.mp h1
      have : m * e' = e' * m := by
        calc m * e' = m * e' * m⁻¹ * e'⁻¹ * (e' * m) := by group
          _ = e' * m := by rw [hx1, one_mul]
      have := congrArg Subtype.val this
      simpa [he'] using this.symm
    · have hdvd : orderOf m ∣ Nat.card M := by
        have := orderOf_dvd_natCard (⟨m, hm⟩ : M)
        rwa [Subgroup.orderOf_mk] at this
      rw [Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hModd hdvd
  · apply le_sSup
    refine ⟨⟨fun k hk n => ?_⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hk ⊢
      obtain ⟨hkC, hkodd⟩ := (hKiff _).mp hk
      rw [hKiff]
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro e he
        have hne : (n : G)⁻¹ * e * n ∈ E := by
          have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem n.2) e).mp he
          simpa using this
        have hk' := Subgroup.mem_centralizer_iff.mp hkC _ hne
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc e * ((n : G) * k * (n : G)⁻¹) = n * ((n : G)⁻¹ * e * n * k) * (n : G)⁻¹ := by group
          _ = n * (k * ((n : G)⁻¹ * e * n)) * (n : G)⁻¹ := by rw [hk']
          _ = (n : G) * k * (n : G)⁻¹ * e := by group
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [show (n : G) * k * (n : G)⁻¹ = MulAut.conj (n : G) (k : G) from rfl,
          show orderOf ((MulAut.conj (n : G)) (k : G)) = orderOf (k : G) from
            orderOf_injective (MulAut.conj (n : G)).toMonoidHom (MulAut.conj (n : G)).injective
              (k : G)]
        exact hkodd
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv]
      exact hKodd

theorem stroth10_aux (hE : IsE 4 ↥E) {N : Subgroup G} (hNE : N = Subgroup.normalizer (E : Set G))
    (φ : ↥N →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf N)
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E) :
    Subgroup.centralizer (E : Set G) = E ⊔ (CFSG.oddCore ↥N).map N.subtype ∧
    ∃ θ : (↥N ⧸ CFSG.oddCore ↥N) →* Equiv.Perm (Fin 6),
      Function.Surjective θ ∧
      θ.ker = (E.subgroupOf N).map (QuotientGroup.mk' (CFSG.oddCore ↥N)) ∧
      ∃ ψ : Multiplicative (altHeart 6) ≃* θ.ker,
        ∀ g (v : Multiplicative (altHeart 6)), g * (ψ v : _) * g⁻¹ =
          (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : _) := by
  classical
  obtain ⟨K, hKC, hKodd, hKiff, hdec, hCEK⟩ := exists_odd_complement_centralizer hE hsyl
  have hO : CFSG.oddCore ↥N = K.subgroupOf N := by
    subst hNE
    exact oddCore_normalizer_eq hE hKC hKodd hKiff
  have hKN : K ≤ N := hNE ▸ hKC.trans centralizer_le_normalizer_set
  have hEN : E ≤ N := hNE ▸ Subgroup.le_normalizer
  have hOmap : (CFSG.oddCore ↥N).map N.subtype = K := by
    rw [hO, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKN]
  refine ⟨by rw [hOmap]; exact hCEK, ?_⟩
  have hOker : CFSG.oddCore ↥N ≤ φ.ker := by
    rw [hO, hker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hKC hx
  set θ₀ := QuotientGroup.lift (CFSG.oddCore ↥N) φ hOker with hθ₀
  have hθ₀ker : θ₀.ker = (E.subgroupOf N).map (QuotientGroup.mk' (CFSG.oddCore ↥N)) := by
    rw [hθ₀, QuotientGroup.ker_lift, hker]
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      obtain ⟨e, he, k, hk, hcek⟩ := hdec _ (Subgroup.mem_subgroupOf.mp hc)
      have hck : c = ⟨e, hEN he⟩ * ⟨k, hKN hk⟩ := Subtype.ext hcek
      have hk1 : QuotientGroup.mk' (CFSG.oddCore ↥N) (⟨k, hKN hk⟩ : ↥N) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO, Subgroup.mem_subgroupOf]
        exact hk
      refine ⟨⟨e, hEN he⟩, Subgroup.mem_subgroupOf.mpr he, ?_⟩
      rw [hck, map_mul, hk1, mul_one]
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨e, Subgroup.mem_subgroupOf.mpr (hsyl.1 (Subgroup.mem_subgroupOf.mp he)), rfl⟩
  haveI hEn : (E.subgroupOf N).Normal := by
    subst hNE
    exact Subgroup.normal_in_normalizer
  letI : CommGroup ↥(E.subgroupOf N) :=
    { (inferInstance : Group ↥(E.subgroupOf N)) with
      mul_comm := fun x y => Subtype.ext (Subtype.ext (mul_comm_of_isE hE
        (Subgroup.mem_subgroupOf.mp x.2) (Subgroup.mem_subgroupOf.mp y.2))) }
  have h2 : ∀ v : ↥(E.subgroupOf N), v * v = 1 := fun v =>
    Subtype.ext (Subtype.ext (mul_self_of_isE hE (Subgroup.mem_subgroupOf.mp v.2)))
  have hcard : Nat.card ↥(E.subgroupOf N) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hE.2]
    norm_num
  set conjE : ↥N →* MulAut ↥(E.subgroupOf N) := MulAut.conjNormal with hconjE
  have hconj_apply : ∀ (n : ↥N) (x : ↥(E.subgroupOf N)),
      (((conjE n x : ↥(E.subgroupOf N)) : ↥N) : G) = n * x * (n : G)⁻¹ := by
    intro n x
    rw [hconjE, MulAut.conjNormal_apply]
    rfl
  have hconjker : φ.ker ≤ conjE.ker := by
    intro n hn
    rw [hker, Subgroup.mem_subgroupOf] at hn
    rw [MonoidHom.mem_ker]
    ext x
    rw [hconj_apply, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp hn _ (Subgroup.mem_subgroupOf.mp x.2)
    rw [← this, mul_inv_cancel_right]
  set ρ : Equiv.Perm (Fin 6) →* MulAut ↥(E.subgroupOf N) :=
    (QuotientGroup.lift φ.ker conjE hconjker).comp
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom with hρ
  have hρφ : ∀ n : ↥N, ρ (φ n) = conjE n := by
    intro n
    have hs : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ n) =
        QuotientGroup.mk' φ.ker n := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hρ, MonoidHom.comp_apply]
    erw [hs]
    rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨n, rfl⟩ := hφ σ
    rw [hρφ] at hσ
    have hn : n ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro e he
      have := congrArg (fun a : MulAut ↥(E.subgroupOf N) =>
        (((a ⟨⟨e, hEN he⟩, Subgroup.mem_subgroupOf.mpr he⟩ : ↥(E.subgroupOf N)) : ↥N) : G)) hσ
      simp only [hconj_apply, MulAut.one_apply] at this
      calc e * n = (n : G) * e * (n : G)⁻¹ * n := by rw [this]
        _ = n * e := by group
    exact hn
  obtain ⟨β, ψ₀, hψ₀⟩ := exists_mulEquiv_altHeart_of_injective h2 hcard ρ hρinj
  set θ := (β.symm : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)).toMonoidHom.comp θ₀ with hθ
  have hθmk : ∀ n : ↥N, θ (QuotientGroup.mk' (CFSG.oddCore ↥N) n) = β.symm (φ n) := fun n => rfl
  have hθsurj : Function.Surjective θ := by
    intro σ
    obtain ⟨n, hn⟩ := hφ (β σ)
    exact ⟨QuotientGroup.mk' _ n, by rw [hθmk, hn, MulEquiv.symm_apply_apply]⟩
  have hθker : θ.ker = θ₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hθ, MonoidHom.comp_apply]
    exact map_eq_one_iff _ β.symm.injective
  set ι : ↥(E.subgroupOf N) →* ↥N ⧸ CFSG.oddCore ↥N :=
    (QuotientGroup.mk' (CFSG.oddCore ↥N)).comp (E.subgroupOf N).subtype with hι
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : ↥N) ∈ CFSG.oddCore ↥N := (QuotientGroup.eq_one_iff _).mp hx
    rw [hO, Subgroup.mem_subgroupOf, hKiff] at hxO
    have hord : orderOf (((x : ↥N) : G)) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact mul_self_of_isE hE (Subgroup.mem_subgroupOf.mp x.2)
    have h1 : orderOf (((x : ↥N) : G)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact h
      · rw [h] at hxO; exact absurd hxO.2 (by decide)
    exact Subtype.ext (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hιrange : ι.range = θ.ker := by
    rw [hθker, hθ₀ker, hι, MonoidHom.range_comp, Subgroup.range_subtype]
  let ψ₁ : ↥(E.subgroupOf N) ≃* ↥θ.ker :=
    (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hιrange)
  refine ⟨θ, hθsurj, hθker.trans hθ₀ker, ψ₀.trans ψ₁, fun g v => ?_⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥N) g
  have hψ : ∀ w, (((ψ₀.trans ψ₁) w : ↥θ.ker) : ↥N ⧸ CFSG.oddCore ↥N) = ι (ψ₀ w) := fun w => rfl
  rw [hψ, hψ, hψ₀, hθmk, MulEquiv.apply_symm_apply, hρφ, hι, MonoidHom.comp_apply,
    MonoidHom.comp_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem stroth10_holds (hE : IsE 4 ↥E)
    (φ : ↥(Subgroup.normalizer (E : Set G)) →* Equiv.Perm (Fin 6)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G)))
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E) :
    Subgroup.centralizer (E : Set G) = E ⊔ (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G))).map
        (Subgroup.normalizer (E : Set G)).subtype ∧
    ∃ θ : (↥(Subgroup.normalizer (E : Set G)) ⧸ CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))
        →* Equiv.Perm (Fin 6),
      Function.Surjective θ ∧
      θ.ker = (E.subgroupOf (Subgroup.normalizer (E : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(Subgroup.normalizer (E : Set G)))) ∧
      ∃ ψ : Multiplicative (altHeart 6) ≃* θ.ker,
        ∀ g (v : Multiplicative (altHeart 6)), g * (ψ v : _) * g⁻¹ =
          (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : _) :=
  stroth10_aux hE rfl φ hφ hker hsyl

end CFSG.CGT.Stroth77
