module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Interface
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.I1420

structure LieCompsExport (q : ℕ) {S : Type} [Group S] (β : MulAut S) : Prop where
  layer : PerfectInLayer β
  comps : ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
    ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X

theorem LieCompExport.toComps {q : ℕ} {S : Type} [Group S] {β : MulAut S}
    (h : LieCompExport q β) : LieCompsExport q β :=
  ⟨h.layer, h.comps⟩

private theorem exists_perfect_map_eq_top {H F : Type*} [Group H] [Finite H] [Group F]
    (π : H →* F) (hπ : Function.Surjective π) (hF : commutator F = ⊤) :
    ∃ P : Subgroup H, ⁅P, P⁆ = P ∧ P.map π = ⊤ := by
  classical
  have hex : ∃ n, ∃ P : Subgroup H, P.map π = ⊤ ∧ Nat.card P = n :=
    ⟨_, ⊤, by rw [Subgroup.map_top]; exact MonoidHom.range_eq_top_of_surjective π hπ, rfl⟩
  obtain ⟨P, hP, hPn⟩ := Nat.find_spec hex
  refine ⟨P, ?_, hP⟩
  have h1 : (⁅P, P⁆).map π = ⊤ := by
    rw [Subgroup.map_commutator, hP, ← _root_.commutator_def]
    exact hF
  have h2 : Nat.find hex ≤ Nat.card (⁅P, P⁆ : Subgroup H) := Nat.find_min' hex ⟨⁅P, P⁆, h1, rfl⟩
  have hle : ⁅P, P⁆ ≤ P := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  exact Subgroup.eq_of_le_of_card_ge hle (hPn ▸ h2)

private theorem mem_sup_of_commute {G : Type*} [Group G] {A Z : Subgroup G}
    (h : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a) {x : G} (hx : x ∈ A ⊔ Z) :
    ∃ a ∈ A, ∃ z ∈ Z, x = a * z := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, Z.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, Z.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    obtain ⟨a', ha', z', hz', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', z * z', Z.mul_mem hz hz', ?_⟩
    have := h a' ha' z hz
    calc a * z * (a' * z') = a * (z * a') * z' := by group
      _ = a * (a' * z) * z' := by rw [this]
      _ = a * a' * (z * z') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, z⁻¹, Z.inv_mem hz, ?_⟩
    have := h a ha z hz
    calc (a * z)⁻¹ = (z * a)⁻¹ := by rw [this]
      _ = a⁻¹ * z⁻¹ := by group

private theorem exists_component_onto {S : Type} [Group S] [Finite S] {C H : Subgroup S}
    (hHC : IsSubnormal H C)
    (hlayer : ∀ P : Subgroup S, P ≤ C → ⁅P, P⁆ = P → P ≤ GLALayer C)
    {F : Type} [Group F] [IsSimpleGroup F] (hna : ∃ a b : F, a * b ≠ b * a)
    (ψ : ↥H →* F) (hψ : Function.Surjective ψ) :
    ∃ (K : Subgroup S) (hKH : K ≤ H), IsComponentOf K C ∧
      Function.Surjective (ψ.comp (Subgroup.inclusion hKH)) := by
  have hFperf : commutator F = ⊤ := (b3Lie_isQuasisimple_of_simple hna).1
  have hZF : Subgroup.center F = ⊥ := b3Lie_center_eq_bot hna
  obtain ⟨P, hPP, hPψ⟩ := exists_perfect_map_eq_top ψ hψ hFperf
  by_contra hno'
  have hno : ∀ (K : Subgroup S) (hKH : K ≤ H), IsComponentOf K C →
      ¬ Function.Surjective (ψ.comp (Subgroup.inclusion hKH)) :=
    fun K hKH hK hs => hno' ⟨K, hKH, hK, hs⟩
  have hHle : H ≤ C := hHC.le
  have step1 : ∀ (K : Subgroup S) (hKH : K ≤ H), IsComponentOf K C →
      ∀ k : ↥K, ψ (Subgroup.inclusion hKH k) = 1 := by
    intro K hKH hK k
    have hKsub : IsSubnormal K H := by
      have := hK.2.1.inf_of_le hHle
      rwa [inf_eq_left.2 hKH] at this
    have hsn : ((K.subgroupOf H).map ψ).IsSubnormal := (hKsub.subgroupOf).map hψ
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsn with h | h
    · have hmem : ψ (Subgroup.inclusion hKH k) ∈ (K.subgroupOf H).map ψ :=
        Subgroup.mem_map_of_mem ψ (show Subgroup.inclusion hKH k ∈ K.subgroupOf H from k.2)
      rw [h] at hmem
      exact (Subgroup.mem_bot).1 hmem
    · exfalso
      refine hno K hKH hK fun f => ?_
      have hf : f ∈ (K.subgroupOf H).map ψ := h ▸ Subgroup.mem_top f
      obtain ⟨y, hy, rfl⟩ := hf
      exact ⟨⟨y.1, hy⟩, rfl⟩
  set A : Subgroup S := ψ.ker.map H.subtype with hA
  set Z : Subgroup S := Subgroup.centralizer (H : Set S) with hZ
  have hAZ : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := by
    rintro _ ⟨a, ha, rfl⟩ z hz
    exact Subgroup.mem_centralizer_iff.1 hz a a.2
  have hlay : GLALayer C ≤ A ⊔ Z := by
    refine sSup_le fun K hK => ?_
    by_cases hKH : K ≤ H
    · refine le_sup_of_le_left ?_
      intro k hk
      exact ⟨⟨k, hKH hk⟩, (MonoidHom.mem_ker).2 (step1 K hKH hK ⟨k, hk⟩), rfl⟩
    · refine le_sup_of_le_right ?_
      rcases b3Lie_comp_le_or_comm hK hHle hHC with h | h
      · exact absurd h hKH
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have step3 : ∀ p ∈ P, ψ p = 1 := by
    intro p hp
    have hP'C : P.map H.subtype ≤ C := (Subgroup.map_subtype_le P).trans hHle
    have hP'perf : ⁅P.map H.subtype, P.map H.subtype⁆ = P.map H.subtype := by
      rw [← Subgroup.map_commutator, hPP]
    have hx : (p : S) ∈ A ⊔ Z := hlay (hlayer _ hP'C hP'perf ⟨p, hp, rfl⟩)
    obtain ⟨a, ha, z, hz, hpaz⟩ := mem_sup_of_commute hAZ hx
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨zH, hzH⟩ : ∃ zH : ↥H, zH = a'⁻¹ * p := ⟨_, rfl⟩
    have hpa : p = a' * zH := by rw [hzH]; group
    have hzHz : (zH : S) = z := by
      have h1 : (p : S) = (a' : S) * (zH : S) := congrArg (fun x : ↥H => (x : S)) hpa
      exact mul_left_cancel (h1.symm.trans hpaz)
    have hcen : ψ zH ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro f
      obtain ⟨y, rfl⟩ := hψ f
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (y : S) * (zH : S) = (zH : S) * (y : S)
      rw [hzHz]
      exact Subgroup.mem_centralizer_iff.1 hz y y.2
    rw [hZF, Subgroup.mem_bot] at hcen
    have ha1 : ψ a' = 1 := (MonoidHom.mem_ker).1 ha'
    rw [hpa, map_mul, ha1, hcen, one_mul]
  obtain ⟨a, b, hab⟩ := hna
  apply hab
  have hone : ∀ f : F, f = 1 := fun f => by
    have hf : f ∈ P.map ψ := hPψ ▸ Subgroup.mem_top f
    obtain ⟨p, hp, rfl⟩ := hf
    exact step3 p hp
  rw [hone a, hone b]

private theorem commute_pCore_of_isSubnormal {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {A : Subgroup G} (hA : A.IsSubnormal) (hcop : Nat.Coprime p (Nat.card A)) :
    ∀ a ∈ A, ∀ r ∈ CFSG.pCore p G, a * r = r * a := by
  set π : Set Nat.Primes := {q | q.val ≠ p} with hπ
  have hAπ : CFSG.IsPiSubgroup π A := by
    intro q hq hqp
    have hp : p ∣ Nat.card A := hqp ▸ hq
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hp)
  have htop : (⊤ : Subgroup ↥A) ≤ CFSG.piCore π ↥A :=
    CFSG.LocalCores.le_piCore_of_normal inferInstance fun q hq =>
      hAπ q (by simpa [Subgroup.card_top] using hq)
  have hint := CFSG.LocalCores.prime_set_core_subnormal_intersection π hA
  have hAle : ∀ a ∈ A, a ∈ CFSG.piCore π G := by
    intro a ha
    have h1 : a ∈ (CFSG.piCore π ↥A).map A.subtype :=
      ⟨⟨a, ha⟩, htop (Subgroup.mem_top _), rfl⟩
    rw [hint] at h1
    exact h1.2
  have hTR : CFSG.piCore π G ⊓ CFSG.pCore p G = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1
      ((CFSG.pCore_isPGroup (p := p) (G := G)).to_le
        (inf_le_right : CFSG.piCore π G ⊓ CFSG.pCore p G ≤ CFSG.pCore p G))
    have hdvd := Subgroup.card_dvd_of_le
      (inf_le_left : CFSG.piCore π G ⊓ CFSG.pCore p G ≤ CFSG.piCore π G)
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [hn, h0]; simp
    · exfalso
      have hp : p ∣ Nat.card (CFSG.piCore π G) :=
        (dvd_pow_self p hpos.ne').trans (hn ▸ hdvd)
      exact (CFSG.LocalCores.piCore_isPiSubgroup π ⟨p, Fact.out⟩ hp) rfl
  intro a ha r hr
  have h1 := Subgroup.commutator_mem_commutator (hAle a ha) hr
  have h2 := Subgroup.commutator_le_inf (CFSG.piCore π G) (CFSG.pCore p G) h1
  rw [hTR, Subgroup.mem_bot] at h2
  exact commutatorElement_eq_one_iff_mul_comm.1 h2


private theorem fi22_noncomm : ∃ a b : Fi22G, a * b ≠ b * a := by
  obtain ⟨hsimp, hcard⟩ := fi22_facts
  by_contra h
  push Not at h
  have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => h a b⟩ hsimp
  rw [hcard] at hprime
  exact absurd hprime (by norm_num)

private theorem not_isChevSimple_fi22 (hb : LieOrderBridge) {q : ℕ} :
    ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q Fi22G := by
  obtain ⟨-, hcard⟩ := fi22_facts
  have hLie : ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty (Fi22G ≃* (TauCeti.CFSGIndex.lie d).Group) → False :=
    fun d hf => not_fi22IsLie hb ⟨d, hf⟩
  rintro (⟨i, hi, hf⟩ | ⟨i, hi, hf⟩)
  · cases i with
    | lie d => exact hLie d hf
    | _ => exact False.elim hi
  · cases i with
    | lie d => exact hLie d hf
    | alternating n hn =>
      obtain ⟨f⟩ := hf
      have hc : Nat.card Fi22G = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr f.toEquiv
      rw [hcard] at hc
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hc
        norm_num [Nat.factorial] at hc
    | _ => exact False.elim hi

theorem false_of_fi22Cfg_of_comps (hb : LieOrderBridge) {q : ℕ} {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : LieCompsExport q α) (hF : Fi22Cfg S α) : False := by
  obtain ⟨hsimp, -⟩ := fi22_facts
  haveI := hsimp
  have hna := fi22_noncomm
  obtain ⟨H, hHsub, N, hN, -, ⟨e⟩⟩ := hF
  have hfix : fixedSub α = fixSubgroup α := by ext s; exact Iff.rfl
  rw [hfix] at hHsub
  let π : ↥H →* Fi22G := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective N)
  obtain ⟨K, hKH, hK, hKsurj⟩ :=
    exists_component_onto hHsub (fun P hP hPP => h.layer P hP hPP) hna π hπ
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps K hK
  let ρ : ↥K →* Fi22G := π.comp (Subgroup.inclusion hKH)
  have hρker : ρ.ker ≤ Subgroup.center ↥K := by
    refine CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hK.2.2 ρ.ker ?_
    intro htop
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have hone : ∀ g : Fi22G, g = 1 := fun g => by
      obtain ⟨k, rfl⟩ := hKsurj g
      exact (MonoidHom.mem_ker).1 (htop ▸ Subgroup.mem_top k)
    rw [hone a, hone b]
  let g : X →* Fi22G := ρ.comp f
  have hg : Function.Surjective g := hKsurj.comp hf
  have hgker : g.ker ≤ Subgroup.center X := by
    intro x hx
    have h1 : f x ∈ Subgroup.center ↥K := hρker ((MonoidHom.mem_ker).2 hx)
    rw [← comap_center_of_surjective hX.perfect f hf hfk]
    exact h1
  have hcomp := hX.lieCompData g hg hgker
  have hcenFi : Subgroup.center Fi22G = ⊥ := b3Lie_center_eq_bot hna
  have e2 : (Fi22G ⧸ Subgroup.center Fi22G) ≃* Fi22G :=
    (QuotientGroup.quotientMulEquivOfEq hcenFi).trans QuotientGroup.quotientBot
  exact not_isChevSimple_fi22 hb (isChevSimple_congr e2 hcomp.chev)

theorem false_of_fi22Cfg_of_unipotent (hQ : YS08.LieQ.LieQConstrainedInner 5) {S : Type}
    [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (hS : IsChevOfChar 5 S) {x : S} (hx1 : x ≠ 1) (hx5 : x ^ 5 = 1)
    (hF : Fi22Cfg S (MulAut.conj x)) : False := by
  obtain ⟨hsimp, hcard⟩ := fi22_facts
  haveI := hsimp
  have hnaF := fi22_noncomm
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Q : Subgroup S := Subgroup.zpowers x with hQdef
  have hQne : Q ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.1 h)
  have hQp : IsPGroup 5 ↥Q := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx5, one_zpow]
  have hQc := hQ S hs hna hS Q hQne hQp
  set Nn : Subgroup S := Subgroup.normalizer (Q : Set S) with hNn
  set R : Subgroup S := pCoreOf 5 Nn with hR
  obtain ⟨H, hHsub, N₀, hN₀, hcop, ⟨e⟩⟩ := hF
  set C : Subgroup S := fixedSub (MulAut.conj x) with hC
  have hCmem : ∀ c : S, c ∈ C ↔ c * x = x * c := by
    intro c
    show MulAut.conj x c = c ↔ _
    rw [MulAut.conj_apply]
    constructor
    · intro h
      calc c * x = (x * c * x⁻¹) * x := by rw [h]
        _ = x * c := by group
    · intro h
      calc x * c * x⁻¹ = (c * x) * x⁻¹ := by rw [h]
        _ = c := by group
  have hcQ : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c := by
    intro c hc q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have hcx : Commute c x := (hCmem c).1 hc
    exact (hcx.zpow_right k).eq
  have hCN : C ≤ Nn := by
    intro c hc
    rw [hNn, Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have : c * q * c⁻¹ = q := by rw [hcQ c hc q hq]; group
      rw [this]
      exact hq
    · intro hq
      have h1 := hcQ c hc _ hq
      have h2 : c * (c * q * c⁻¹) = c * q := by rw [h1]; group
      have h3 : c * q * c⁻¹ = q := mul_left_cancel h2
      rw [h3] at hq
      exact hq
  have hCnormal : (C.subgroupOf Nn).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCN]
    intro c g hc hg
    rw [hCmem]
    have hx' : g⁻¹ * x * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (Nn.inv_mem hg) x).1 (Subgroup.mem_zpowers x)
      simpa using this
    have hcom : c * (g⁻¹ * x * g) = (g⁻¹ * x * g) * c := hcQ c hc _ hx'
    calc g * c * g⁻¹ * x = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by rw [hcom]
      _ = x * (g * c * g⁻¹) := by group
  have hCNsub : IsSubnormal C Nn := IsSubnormal.step hCN hCnormal (IsSubnormal.refl Nn)
  have hHC : H ≤ C := hHsub.le
  have hHN : H ≤ Nn := hHC.trans hCN
  have hHNsub : IsSubnormal H Nn := hHsub.trans hCNsub
  set A : Subgroup S := N₀.map H.subtype with hA
  have hAH : A ≤ H := Subgroup.map_subtype_le N₀
  have hAHsub : IsSubnormal A H := by
    refine IsSubnormal.step hAH ?_ (IsSubnormal.refl H)
    rw [show A.subgroupOf H = N₀ from Subgroup.comap_map_eq_self_of_injective H.subtype_injective N₀]
    exact hN₀
  have hANsub : IsSubnormal A Nn := hAHsub.trans hHNsub
  have hAN : A ≤ Nn := hAH.trans hHN
  have hcardA : Nat.card A = Nat.card N₀ := Subgroup.card_map_of_injective H.subtype_injective
  have hcopA : Nat.Coprime 5 (Nat.card (A.subgroupOf Nn)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hcardA]
    exact hcop
  have hAn : (A.subgroupOf Nn).IsSubnormal := hANsub.subgroupOf
  have hRp : IsPGroup 5 ↥R := (CFSG.pCore_isPGroup (p := 5) (G := ↥Nn)).map Nn.subtype
  have hAR : A ≤ R := by
    intro a ha
    have haNn : a ∈ Nn := hAN ha
    refine hQc a haNn fun r hr => ?_
    obtain ⟨r', hr', rfl⟩ := hr
    have hmem : (⟨a, haNn⟩ : ↥Nn) ∈ A.subgroupOf Nn := ha
    exact congrArg Subtype.val (commute_pCore_of_isSubnormal hAn hcopA _ hmem r' hr')
  have hAp : IsPGroup 5 ↥A := hRp.to_le hAR
  have hN₀bot : N₀ = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hAp
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [← hcardA, hn, h0]; simp
    · exfalso
      have h5 : 5 ∣ Nat.card N₀ := hcardA ▸ hn ▸ dvd_pow_self 5 hpos.ne'
      have := Nat.Coprime.eq_one_of_dvd hcop h5
      omega
  let eH : ↥H ≃* Fi22G :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hN₀bot.symm)).trans e
  have hHq : CFSG.Open.IsQuasisimple ↥H :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eH (b3Lie_isQuasisimple_of_simple hnaF)
  have hHcomp : IsComponentOf H Nn := ⟨hHN, hHNsub, hHq⟩
  have hRle : R ≤ Nn := Subgroup.map_subtype_le _
  have hRsub : IsSubnormal R Nn := by
    refine IsSubnormal.step hRle ?_ (IsSubnormal.refl Nn)
    rw [show R.subgroupOf Nn = CFSG.pCore 5 ↥Nn from
      Subgroup.comap_map_eq_self_of_injective Nn.subtype_injective _]
    exact CFSG.pCore_normal
  have hHR : H ≤ R := by
    rcases b3Lie_comp_le_or_comm hHcomp hRle hRsub with h | h
    · exact h
    · intro y hy
      refine hQc y (hHN hy) fun r hr => ?_
      have hy' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hy
      exact ((Subgroup.mem_centralizer_iff.1 hy') r hr).symm
  have hHp : IsPGroup 5 ↥H := hRp.to_le hHR
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hHp
  rw [Nat.card_congr eH.toEquiv, hcard] at hn
  have h2 : 2 ∣ 5 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

theorem fi22LieUnipC_of_lieQ (hQ : YS08.LieQ.LieQConstrainedInner 5) : Fi22LieUnipC := by
  intro S _ _ _ hna idx hidx hchar x hx5 hx1 hF
  exfalso
  have hS : IsChevOfChar 5 S := by
    refine ⟨idx, YS08.isChevIndexOfChar_of_lieIndexChar_eq ?_, hidx⟩
    rw [← hchar]
    cases idx.1 <;> simp [lieIndexChar]
  exact false_of_fi22Cfg_of_unipotent hQ inferInstance hna hS hx1 hx5 hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
