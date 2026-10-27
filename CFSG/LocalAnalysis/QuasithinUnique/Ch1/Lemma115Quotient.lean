module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Datum
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.A1a

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Open CFSG.QuasithinUnique

section PGroupQuotient

variable {K : Type*} [Group K]

theorem charTwo_of_normal_of_forall_pow_mem {D X : Subgroup K} (hDX : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hq : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ D) (hD : CharTwo D) :
    CharTwo X := by
  set Q := pCoreOf 2 X with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set K) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hDQ : pCoreOf 2 D ≤ Q :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 D X hDX hn
  set Y : Subgroup K := X ⊓ Subgroup.centralizer (Q : Set K) with hY
  have hYX : Y ≤ X := inf_le_left
  have hXY : X ≤ Subgroup.normalizer (Y : Set K) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf X X _
      Subgroup.le_normalizer
      (hXQ.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer Q))
  have hYp : IsPGroup 2 Y := by
    intro y
    obtain ⟨n, hn'⟩ := hq (y : K) (hYX y.2)
    have hyn : ((y : K) ^ 2 ^ n) ∈ D ⊓ Subgroup.centralizer (pCoreOf 2 D : Set K) := by
      refine ⟨hn', ?_⟩
      have h1 : (y : K) ^ 2 ^ n ∈ Subgroup.centralizer (Q : Set K) :=
        Subgroup.pow_mem _ y.2.2 _
      exact Subgroup.centralizer_le (by exact_mod_cast hDQ) h1
    have hyQ : (y : K) ^ 2 ^ n ∈ Q := hDQ (hD hyn)
    obtain ⟨m, hm⟩ := hQ2 ⟨_, hyQ⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have h2 : ((y : K) ^ 2 ^ n) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [← pow_mul, ← pow_add] at h2
    simpa using h2
  have hYQ : Y ≤ Q := CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hYX hXY hYp
  exact fun y hy => hYQ hy

end PGroupQuotient

section CentralImage

theorem charTwoInternal_of_surjective_central_kernel {C D : Type*} [Group C] [Group D] [Finite C]
    (f : C →* D) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center C)
    (h : Subgroup.centralizer (CFSG.Open.pCore 2 C : Set C) ≤ CFSG.Open.pCore 2 C) :
    Subgroup.centralizer (CFSG.Open.pCore 2 D : Set D) ≤ CFSG.Open.pCore 2 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.Quasithin.centralizer_pCore_quotient_le (p := 2) f.ker hker h
  exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
    (QuotientGroup.quotientKerEquivOfSurjective f hf) h1

end CentralImage

section Quotient

variable {L : Type} [Group L] [Finite L] {α : L ≃* L}

theorem InvDatum.charTwo_quotient (h : InvDatum L α) : CharTwo (fixedSubgroup (quotAut α)) := by
  set π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L) with hπ
  set C : Subgroup L := fixedSubgroup α with hC
  set D : Subgroup (L ⧸ Subgroup.center L) := C.map π with hD
  set X : Subgroup (L ⧸ Subgroup.center L) := fixedSubgroup (quotAut α) with hX
  have hdisp : ∀ x : L, (QuotientGroup.mk x : L ⧸ Subgroup.center L) ∈ X →
      x⁻¹ * α x ∈ Subgroup.center L := by
    intro x hx
    have h1 : quotAut α (QuotientGroup.mk x) = QuotientGroup.mk x := hx
    rw [quotAut_mk, QuotientGroup.eq] at h1
    simpa using Subgroup.inv_mem _ h1
  have hDX : D ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    show quotAut α (QuotientGroup.mk y) = QuotientGroup.mk y
    have hy' : α y = y := hy
    rw [quotAut_mk, hy']
  have hn : (D.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDX, Subgroup.le_normalizer_iff]
    intro x hx d hd
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, hy, rfl⟩ := hd
    have hc := hdisp x₀ hx
    refine ⟨x₀ * y * x₀⁻¹, ?_, rfl⟩
    show α (x₀ * y * x₀⁻¹) = x₀ * y * x₀⁻¹
    have hα : α y = y := hy
    set c := x₀⁻¹ * α x₀ with hcdef
    have hax : α x₀ = x₀ * c := by rw [hcdef]; group
    have hcy : c * y = y * c := (Subgroup.mem_center_iff.mp hc y).symm
    rw [map_mul, map_mul, map_inv, hα, hax]
    calc x₀ * c * y * (x₀ * c)⁻¹ = x₀ * (c * y) * c⁻¹ * x₀⁻¹ := by group
      _ = x₀ * (y * c) * c⁻¹ * x₀⁻¹ := by rw [hcy]
      _ = x₀ * y * x₀⁻¹ := by group
  have hq : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ D := by
    intro x hx
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
    have hc := hdisp x₀ hx
    set c := x₀⁻¹ * α x₀ with hcdef
    have hax : α x₀ = x₀ * c := by rw [hcdef]; group
    have hcomm : Commute x₀ c := Subgroup.mem_center_iff.mp hc x₀
    obtain ⟨a, u, hu, hord⟩ :=
      Nat.exists_eq_two_pow_mul_odd (isOfFinOrder_of_finite c).orderOf_pos.ne'
    obtain ⟨j, rfl⟩ := hu
    refine ⟨a, ?_⟩
    set b := c ^ 2 ^ a with hb
    have hb1 : b ^ (2 * j + 1) = 1 := by
      rw [hb, ← pow_mul, ← hord, pow_orderOf_eq_one]
    set z := b ^ (j + 1) with hz
    have hz2 : z * z = b := by
      rw [hz, ← pow_add, show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, hb1, one_mul]
    have hzc : z ∈ Subgroup.center L :=
      Subgroup.pow_mem _ (Subgroup.pow_mem _ hc _) _
    have hzodd : Odd (orderOf z) := by
      have hz1 : z ^ (2 * j + 1) = 1 := by
        rw [hz, ← pow_mul, mul_comm, pow_mul, hb1, one_pow]
      exact Odd.of_dvd_nat (by exact ⟨j, rfl⟩) (orderOf_dvd_of_pow_eq_one hz1)
    have hαz : α z = z⁻¹ := h.inverts z hzc hzodd
    refine ⟨x₀ ^ 2 ^ a * z, ?_, ?_⟩
    · show α (x₀ ^ 2 ^ a * z) = x₀ ^ 2 ^ a * z
      rw [map_mul, map_pow, hax, hcomm.mul_pow, hαz]
      calc x₀ ^ 2 ^ a * c ^ 2 ^ a * z⁻¹ = x₀ ^ 2 ^ a * (z * z) * z⁻¹ := by rw [hz2]
        _ = x₀ ^ 2 ^ a * z := by group
    · show π (x₀ ^ 2 ^ a * z) = (QuotientGroup.mk x₀ : L ⧸ Subgroup.center L) ^ 2 ^ a
      rw [map_mul, map_pow]
      have : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hzc
      rw [this, mul_one]
      rfl
  have hDchar : CharTwo D := by
    have hCint : Subgroup.centralizer (CFSG.Open.pCore 2 C : Set C) ≤ CFSG.Open.pCore 2 C :=
      charTwo_iff_internal.mp h.charTwo
    let f : C →* D := (π.comp C.subtype).codRestrict D (fun c => ⟨c, c.2, rfl⟩)
    have hf : Function.Surjective f := by
      rintro ⟨_, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    have hker : f.ker ≤ Subgroup.center C := by
      intro c hc
      have h1 : π (c : L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
      have hcL : (c : L) ∈ Subgroup.center L := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hcL (g : L))
    exact charTwo_iff_internal.mpr (charTwoInternal_of_surjective_central_kernel f hf hker hCint)
  exact charTwo_of_normal_of_forall_pow_mem hDX hn hq hDchar

theorem center_quotient_eq_bot {L : Type} [Group L] (hq : CFSG.IsQuasisimple L) :
    Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
  have hs := hq.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (L ⧸ Subgroup.center L)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a)) b).symm

theorem isQuasisimple_quotient {L : Type} [Group L] (hq : CFSG.IsQuasisimple L) :
    CFSG.IsQuasisimple (L ⧸ Subgroup.center L) := by
  have hbot := center_quotient_eq_bot hq
  have e : (L ⧸ Subgroup.center L) ⧸ Subgroup.center (L ⧸ Subgroup.center L) ≃*
      (L ⧸ Subgroup.center L) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup_congr.mpr hq.2.1, ?_⟩
  · have := hq.1
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _)
  · obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨e.symm a, e.symm b, fun h =>
      hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem InvDatum.quotient (h : InvDatum L α) :
    InvDatum (L ⧸ Subgroup.center L) (quotAut α) := by
  have hbot := center_quotient_eq_bot h.quasisimple
  refine ⟨isQuasisimple_quotient h.quasisimple, h.quotAut_involutory, ?_, h.quotAut_sylow, ?_,
    h.charTwo_quotient⟩
  · obtain ⟨y, hy⟩ := h.quotAut_nontrivial
    refine ⟨y, fun hmem => hy ?_⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  · intro y hy _
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy]
    simp

end Quotient

end CFSG.QuasithinUnique.Ch1
