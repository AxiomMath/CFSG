module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem i1312_le_pCoreOf {G : Type} [Group G] {p : ℕ} (N K : Subgroup G)
    (hKN : K ≤ N) (hKn : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K) (hKp : IsPGroup p K) :
    K ≤ pCoreOf p N := by
  have hnorm : (K.subgroupOf N).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have := hKn g g.2 a ha
    simpa using this
  have hpK : IsPGroup p (K.subgroupOf N) := by
    intro x
    obtain ⟨k, hk⟩ := hKp ⟨x.1.1, (Subgroup.mem_subgroupOf).1 x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : K => (y : G)) hk
    simpa using this
  have h1 : K.subgroupOf N ≤ pCore p ↥N := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hnorm hpK
  have h2 : (K.subgroupOf N).map N.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hy
    · intro hx
      exact ⟨⟨x, hKN hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
  calc K = (K.subgroupOf N).map N.subtype := h2.symm
    _ ≤ pCoreOf p N := Subgroup.map_mono h1

theorem i1312_pCoreOf_normalized {G : Type} [Group G] (p : ℕ) (N : Subgroup G) :
    ∀ n ∈ N, ∀ t ∈ pCoreOf p N, n * t * n⁻¹ ∈ pCoreOf p N := by
  intro n hn t ht
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ht
  refine Subgroup.mem_map.2 ⟨⟨n, hn⟩ * x * ⟨n, hn⟩⁻¹, ?_, ?_⟩
  · exact Subgroup.Normal.conj_mem inferInstance x hx _
  · simp

theorem i1312_isPGroup_subgroupOf {G : Type} [Group G] {p : ℕ} {H K : Subgroup G} (hK : IsPGroup p K) :
    IsPGroup p (K.subgroupOf H) := by
  intro x
  obtain ⟨k, hk⟩ := hK ⟨x.1.1, (Subgroup.mem_subgroupOf).1 x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun y : K => (y : G)) hk
  simpa using this

theorem i1312_pCore_le_Sbar {G : Type} [Group G] [Finite G] {p : ℕ} {I B S : Subgroup G}
    (hp : p.Prime) (hp3 : 3 ≤ p)
    (hBN : B ≤ Subgroup.normalizer (I : Set G)) (hBp : IsPGroup p B)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hSI : S ≤ I) (hS2 : IsPGroup 2 S)
    (hSO : ¬ S ≤ GLAPPrimeCoreOf p I)
    (hmax : ∀ S' : Subgroup G, S ≤ S' → S' ≤ I → IsPGroup 2 S' →
      B ≤ Subgroup.normalizer (S' : Set G) → ¬ S' ≤ GLAPPrimeCoreOf p I → S' = S) :
    pCoreOf 2 (Subgroup.normalizer ((S.subgroupOf I).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) : Set (PQuot p I))) ≤
      (S.subgroupOf I).map (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  set q : ↥I →* PQuot p I := QuotientGroup.mk' (GLAPPrimeCore p ↥I) with hq
  set O : Subgroup G := GLAPPrimeCoreOf p I with hO
  set Sbar : Subgroup (PQuot p I) := (S.subgroupOf I).map q with hSbar
  set Nb : Subgroup (PQuot p I) := Subgroup.normalizer (Sbar : Set (PQuot p I)) with hNb
  set Tbar : Subgroup (PQuot p I) := pCoreOf 2 Nb with hTbar
  have hqO : ∀ x : ↥I, q x = 1 ↔ (x : G) ∈ O := by
    intro x
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact Subgroup.mem_map.2 ⟨x, h, rfl⟩
    · intro h
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
  have hSbarNb : Sbar ≤ Nb := Subgroup.le_normalizer
  have hSbarn : ∀ n ∈ Nb, ∀ k ∈ Sbar, n * k * n⁻¹ ∈ Sbar := by
    intro n hn k hk
    exact (Subgroup.mem_normalizer_iff.1 hn k).1 hk
  have hSbarp : IsPGroup 2 Sbar := IsPGroup.map (i1312_isPGroup_subgroupOf hS2) q
  have hTbarp : IsPGroup 2 Tbar :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥Nb)) Nb.subtype
  have hTbarNb : Tbar ≤ Nb := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hSbarTbar : Sbar ≤ Tbar :=
    i1312_le_pCoreOf Nb Sbar hSbarNb hSbarn hSbarp
  have hbarq : ∀ (b : G) (hb : b ∈ B) (y : ↥I),
      barAut p I ⟨b, hBN hb⟩ (q y) = q (I.normalizerMonoidHom ⟨b, hBN hb⟩ y) :=
    fun b hb y => barAut_mk p I ⟨b, hBN hb⟩ y
  have hσinv : ∀ (b : G) (hb : b ∈ B) (x : PQuot p I),
      barAut p I ⟨b⁻¹, hBN (B.inv_mem hb)⟩ (barAut p I ⟨b, hBN hb⟩ x) = x := by
    intro b hb x
    have h1 : (barAut p I ⟨b⁻¹, hBN (B.inv_mem hb)⟩ * barAut p I ⟨b, hBN hb⟩) = 1 := by
      rw [← map_mul]
      have : (⟨b⁻¹, hBN (B.inv_mem hb)⟩ * ⟨b, hBN hb⟩ : ↥(Subgroup.normalizer (I : Set G))) = 1 :=
        Subtype.ext (inv_mul_cancel b)
      rw [this, map_one]
    have h2 := congrArg (fun φ : MulAut (PQuot p I) => φ x) h1
    simpa [MulAut.mul_apply] using h2
  have hσinv' : ∀ (b : G) (hb : b ∈ B) (x : PQuot p I),
      barAut p I ⟨b, hBN hb⟩ (barAut p I ⟨b⁻¹, hBN (B.inv_mem hb)⟩ x) = x := by
    intro b hb x
    have h1 : (barAut p I ⟨b, hBN hb⟩ * barAut p I ⟨b⁻¹, hBN (B.inv_mem hb)⟩) = 1 := by
      rw [← map_mul]
      have : (⟨b, hBN hb⟩ * ⟨b⁻¹, hBN (B.inv_mem hb)⟩ : ↥(Subgroup.normalizer (I : Set G))) = 1 :=
        Subtype.ext (mul_inv_cancel b)
      rw [this, map_one]
    have h2 := congrArg (fun φ : MulAut (PQuot p I) => φ x) h1
    simpa [MulAut.mul_apply] using h2
  have hσS : ∀ (b : G) (hb : b ∈ B) (x : PQuot p I), x ∈ Sbar →
      barAut p I ⟨b, hBN hb⟩ x ∈ Sbar := by
    intro b hb x hx
    rw [hSbar] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hbarq b hb, hSbar]
    refine Subgroup.mem_map.2 ⟨I.normalizerMonoidHom ⟨b, hBN hb⟩ y, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    rw [chev_coe_normalizerMonoidHom]
    exact (Subgroup.mem_normalizer_iff.1 (hBS hb) (y : G)).1 hy
  have hσS_iff : ∀ (b : G) (hb : b ∈ B) (x : PQuot p I),
      x ∈ Sbar ↔ barAut p I ⟨b, hBN hb⟩ x ∈ Sbar := by
    intro b hb x
    refine ⟨hσS b hb x, fun hx => ?_⟩
    have := hσS b⁻¹ (B.inv_mem hb) _ hx
    rwa [hσinv b hb x] at this
  have hσN : ∀ (b : G) (hb : b ∈ B) (n : PQuot p I), n ∈ Nb →
      barAut p I ⟨b, hBN hb⟩ n ∈ Nb := by
    intro b hb n hn
    rw [hNb, Subgroup.mem_normalizer_iff] at hn ⊢
    intro h
    have key : barAut p I ⟨b, hBN hb⟩ n * h * (barAut p I ⟨b, hBN hb⟩ n)⁻¹ =
        barAut p I ⟨b, hBN hb⟩ (n * barAut p I ⟨b⁻¹, hBN (B.inv_mem hb)⟩ h * n⁻¹) := by
      rw [map_mul, map_mul, map_inv, hσinv' b hb h]
    rw [key]
    exact (hσS_iff b⁻¹ (B.inv_mem hb) h).trans ((hn _).trans (hσS_iff b hb _))
  have hσT : ∀ (b : G) (hb : b ∈ B),
      Tbar.map (barAut p I ⟨b, hBN hb⟩).toMonoidHom ≤ Tbar := by
    intro b hb
    refine (i1312_le_pCoreOf (p := 2) Nb _ ?_ ?_ (hTbarp.map _) : _ ≤ pCoreOf 2 Nb)
    · rintro _ ⟨t, ht, rfl⟩
      exact hσN b hb t (hTbarNb ht)
    · rintro n hn _ ⟨t, ht, rfl⟩
      refine ⟨barAut p I ⟨b⁻¹, hBN (B.inv_mem hb)⟩ n * t *
        (barAut p I ⟨b⁻¹, hBN (B.inv_mem hb)⟩ n)⁻¹, ?_, ?_⟩
      · exact i1312_pCoreOf_normalized 2 Nb _ (hσN b⁻¹ (B.inv_mem hb) n hn) t ht
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hσinv' b hb n]
  set T1 : Subgroup ↥I := Tbar.comap q with hT1
  set Tf : Subgroup G := T1.map I.subtype with hTf
  have hTf_iff : ∀ (x : G) (hx : x ∈ I), x ∈ Tf ↔ q ⟨x, hx⟩ ∈ Tbar := by
    intro x hx
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      rw [this] at hy
      exact hy
    · intro h
      exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, h, rfl⟩
  have hTf_le : Tf ≤ I := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hSTf : S ≤ Tf := fun s hs =>
    (hTf_iff s (hSI hs)).2 (hSbarTbar (Subgroup.mem_map.2 ⟨⟨s, hSI hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩))
  have hOI : O ≤ I := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hOTf : O ≤ Tf := fun o ho => by
    have h1 : q ⟨o, hOI ho⟩ = 1 := (hqO ⟨o, hOI ho⟩).2 ho
    exact (hTf_iff o (hOI ho)).2 (by rw [h1]; exact Tbar.one_mem)
  have hTf_inv : ∀ (b : G) (hb : b ∈ B) (x : G), x ∈ Tf → b * x * b⁻¹ ∈ Tf := by
    intro b hb x hx
    have hxI := hTf_le hx
    have hbxI : b * x * b⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hBN hb) x).1 hxI
    rw [hTf_iff x hxI] at hx
    rw [hTf_iff _ hbxI]
    have := hσT b hb (Subgroup.mem_map.2 ⟨_, hx, rfl⟩)
    simp only [MulEquiv.coe_toMonoidHom] at this
    rw [hbarq b hb] at this
    convert this using 2
    exact Subtype.ext (chev_coe_normalizerMonoidHom ⟨b, hBN hb⟩ ⟨x, hxI⟩).symm

  set O : Subgroup G := GLAPPrimeCoreOf p I with hO
  have hT1card : Nat.card T1 = Nat.card Tbar * Nat.card O := by
    have hidx : T1.index = Tbar.index :=
      Subgroup.index_comap_of_surjective (f := q) Tbar (QuotientGroup.mk'_surjective _)
    have c1 := Subgroup.card_mul_index T1
    have c2 := Subgroup.card_mul_index Tbar
    have c3 : Nat.card ↥I = Nat.card (PQuot p I) * Nat.card (GLAPPrimeCore p ↥I) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have c4 : Nat.card O = Nat.card (GLAPPrimeCore p ↥I) :=
      Subgroup.card_map_of_injective Subtype.val_injective
    have hpos : Tbar.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hidx] at c1
    rw [c4]
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos)
    rw [c1, c3, ← c2]
    ring
  have hTfcard : Nat.card Tf = Nat.card Tbar * Nat.card O := by
    rw [hTf, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hT1card
  have hcop : p.Coprime (Nat.card Tf) := by
    rw [hTfcard]
    apply Nat.Coprime.mul_right
    · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hTbarp
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    · exact CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp I
  let Ψ : ↥B →* MulAut G := (MulAut.conj : G →* MulAut G).comp B.subtype
  have hinvT : ∀ b : ↥B, Tf.map (Ψ b).toMonoidHom = Tf := by
    intro b
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hTf_inv b.1 b.2 x hx
    · rw [Subgroup.card_map_of_injective (f := (Ψ b).toMonoidHom) (MulEquiv.injective (Ψ b))]
  have hSp : IsPGroup 2 ↥(S.subgroupOf Tf) := i1312_isPGroup_subgroupOf hS2
  have hSinv : ∀ element : ↥B,
      (S.subgroupOf Tf).map (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism Ψ Tf hinvT element).toMonoidHom =
        S.subgroupOf Tf := by
    intro b
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.1 (hBS b.2) (x : G)).1 hx
    · rw [Subgroup.card_map_of_injective (f := (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism Ψ Tf hinvT b).toMonoidHom) (MulEquiv.injective _)]
  obtain ⟨P₂, hSP₂, hPinv⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_containing_of_coprime p 2 hBp
      ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)
      (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism Ψ Tf hinvT)
      (S.subgroupOf Tf) hSp hSinv
  set Sg : Subgroup G := (P₂ : Subgroup ↥Tf).map Tf.subtype with hSg
  have hSg2 : IsPGroup 2 Sg := IsPGroup.map P₂.isPGroup' Tf.subtype
  have hSgI : Sg ≤ I := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact hTf_le y.2
  have hdir : ∀ (b : G) (hb : b ∈ B) (x : G), x ∈ Sg → b * x * b⁻¹ ∈ Sg := by
    intro b hb x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 : (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism Ψ Tf hinvT ⟨b, hb⟩).toMonoidHom y ∈
        (P₂ : Subgroup ↥Tf).map (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism Ψ Tf hinvT
          ⟨b, hb⟩).toMonoidHom :=
      Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    rw [hPinv ⟨b, hb⟩] at h1
    exact Subgroup.mem_map.2 ⟨_, h1, rfl⟩
  have hBSg : B ≤ Subgroup.normalizer (Sg : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hdir b hb h
    · intro hh
      have := hdir b⁻¹ (B.inv_mem hb) _ hh
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rw [e] at this
      exact this
  have hSS : S ≤ Sg := fun s hs => by
    have h1 : (⟨s, hSTf hs⟩ : ↥Tf) ∈ S.subgroupOf Tf := Subgroup.mem_subgroupOf.2 hs
    exact Subgroup.mem_map.2 ⟨⟨s, hSTf hs⟩, hSP₂ h1, rfl⟩
  have hSgnO : ¬ Sg ≤ O := fun h => hSO (hSS.trans h)
  have hSg_eq : Sg = S := hmax Sg hSS hSgI hSg2 hBSg hSgnO
  have hScard : Nat.card S = twoPart (Nat.card Tf) := by
    rw [← hSg_eq, hSg, Subgroup.card_map_of_injective (f := Tf.subtype) Subtype.val_injective]
    exact Sylow.card_eq_multiplicity P₂
  have hTwo : twoPart (Nat.card Tf) = Nat.card Tbar * twoPart (Nat.card O) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hTbarp
    rw [hTfcard, i133_twoPart_mul_of_ne (Nat.card_pos.ne') (Nat.card_pos.ne'), hk, twoPart_two_pow]
  set φ : ↥(S.subgroupOf I) →* PQuot p I := q.comp (S.subgroupOf I).subtype with hφ
  have hφrange : φ.range = Sbar := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hSbar]
  have hsplit : Nat.card ↥(S.subgroupOf I) = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hSI_card : Nat.card ↥(S.subgroupOf I) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSI).toEquiv
  have hSI2 : IsPGroup 2 ↥(S.subgroupOf I) := i1312_isPGroup_subgroupOf hS2
  have hkerO : Nat.card φ.ker ≤ twoPart (Nat.card O) := by
    have hle : φ.ker.map (I.subtype.comp (S.subgroupOf I).subtype) ≤ O := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : q ((S.subgroupOf I).subtype x) = 1 := MonoidHom.mem_ker.1 hx
      exact (hqO _).1 h1
    have hinj : Function.Injective (I.subtype.comp (S.subgroupOf I).subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hdvd : Nat.card φ.ker ∣ Nat.card O := by
      rw [← Subgroup.card_map_of_injective (f := I.subtype.comp (S.subgroupOf I).subtype) hinj]
      exact Subgroup.card_dvd_of_le hle
    have hker2 : IsPGroup 2 φ.ker := IsPGroup.to_subgroup hSI2 φ.ker
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hker2
    rw [hk] at hdvd ⊢
    exact i133_pow_two_le_twoPart (Nat.card_pos.ne') hdvd
  have hle : Nat.card Tbar ≤ Nat.card Sbar := by
    have h1 : Nat.card S = Nat.card Sbar * Nat.card φ.ker := by
      rw [← hSI_card, hsplit, hφrange]
    have h2 : Nat.card Tbar * twoPart (Nat.card O) = Nat.card Sbar * Nat.card φ.ker := by
      rw [← hTwo, ← hScard, h1]
    have hpos : 0 < twoPart (Nat.card O) := i133_twoPart_pos _
    have h3 : Nat.card Tbar * twoPart (Nat.card O) ≤ Nat.card Sbar * twoPart (Nat.card O) := by
      rw [h2]
      exact Nat.mul_le_mul_left _ hkerO
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hSbarEq : Sbar = Tbar := Subgroup.eq_of_le_of_card_ge hSbarTbar hle
  exact le_of_eq hSbarEq.symm

end CFSG.LocalAnalysis.GLTheoremA
