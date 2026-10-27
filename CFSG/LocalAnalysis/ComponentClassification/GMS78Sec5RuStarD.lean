module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuInv
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuStarTI

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

theorem jordanGL32_sq_val :
    ((jordanGL32 ^ 2 : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  decide

theorem eq_one_or_eq_sq_of_commute_jordanGL32 {M : GL (Fin 3) (ZMod 2)}
    (hM : M * jordanGL32 = jordanGL32 * M) (hM2 : M ^ 2 = 1) : M = 1 ∨ M = jordanGL32 ^ 2 := by
  have key : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
      A * !![1, 1, 0; 0, 1, 1; 0, 0, 1] = !![1, 1, 0; 0, 1, 1; 0, 0, 1] * A → A * A = 1 →
        A = 1 ∨ A = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    decide +kernel
  have h1 := congrArg Units.val hM
  have h2 := congrArg Units.val hM2
  rw [Units.val_mul, Units.val_mul] at h1
  rw [sq, Units.val_mul, Units.val_one] at h2
  rcases key _ h1 h2 with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (h.trans jordanGL32_sq_val.symm))

theorem exists_conj_jordanGL32_mem {Q : Subgroup (GL (Fin 3) (ZMod 2))} (hQ : Nat.card Q = 8) :
    ∃ g, g * jordanGL32 * g⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ∀ P : Sylow 2 (GL (Fin 3) (ZMod 2)), Nat.card P = 8 := fun P => by
    simpa using LiteratureLocal.Order504.card_sylow_eq_of_card_eq (p := 2) (a := 3) (m := 21)
      (by rw [GHarris.card_GL32_gh]; norm_num) (by norm_num) P
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)
  obtain ⟨P, hP⟩ := hQp.exists_le_sylow
  have hQP : (P : Subgroup (GL (Fin 3) (ZMod 2))) = Q :=
    (eq_of_le_of_card_ge hP (le_of_eq (by rw [hcard, hQ]))).symm
  have hJp : IsPGroup 2 (zpowers jordanGL32) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, orderOf_jordanGL32]; norm_num)
  obtain ⟨P₀, hP₀⟩ := hJp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) P₀ P
  refine ⟨g, ?_⟩
  rw [← hQP, ← hg]
  change g * jordanGL32 * g⁻¹ ∈ ((g • P₀ : Sylow 2 _) : Set (GL (Fin 3) (ZMod 2)))
  rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    show g⁻¹ * (g * jordanGL32 * g⁻¹) * g = jordanGL32 by group]
  exact hP₀ (mem_zpowers jordanGL32)

theorem card_le_four_of_commute_GL32 {P Q : Subgroup (GL (Fin 3) (ZMod 2))} (hP : IsPGroup 2 P)
    (hQ : ∀ q ∈ Q, q ^ 2 = 1) (hQ2 : 2 < Nat.card Q) (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) :
    Nat.card P ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : 2 ^ k ∣ 168 := hk ▸ GHarris.card_GL32_gh ▸ Subgroup.card_subgroup_dvd_card P
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h16 : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h16
  rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | rfl
  · rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  exfalso
  obtain ⟨g, hg⟩ := exists_conj_jordanGL32_mem (Q := P) (by rw [hk]; norm_num)
  have hsub : ∀ q ∈ Q, q = 1 ∨ q = g * jordanGL32 ^ 2 * g⁻¹ := by
    intro q hq
    have hc := hPQ _ hg q hq
    have h1 : g⁻¹ * q * g * jordanGL32 = jordanGL32 * (g⁻¹ * q * g) :=
      calc g⁻¹ * q * g * jordanGL32 = g⁻¹ * (q * (g * jordanGL32 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * jordanGL32 * g⁻¹) * q) * g := by rw [hc]
        _ = jordanGL32 * (g⁻¹ * q * g) := by group
    have h2 : (g⁻¹ * q * g) ^ 2 = 1 := by
      rw [show (g⁻¹ * q * g) ^ 2 = g⁻¹ * q ^ 2 * g by rw [sq, sq]; group, hQ q hq]
      group
    rcases eq_one_or_eq_sq_of_commute_jordanGL32 h1 h2 with h | h
    · refine Or.inl ?_
      calc q = g * (g⁻¹ * q * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · refine Or.inr ?_
      calc q = g * (g⁻¹ * q * g) * g⁻¹ := by group
        _ = g * jordanGL32 ^ 2 * g⁻¹ := by rw [h]
  have hinj : Function.Injective fun q : Q => decide ((q : GL (Fin 3) (ZMod 2)) = 1) := by
    intro q q' hqq'
    simp only [decide_eq_decide] at hqq'
    apply Subtype.ext
    rcases hsub q q.2 with h | h <;> rcases hsub q' q'.2 with h' | h'
    · rw [h, h']
    · rw [h, hqq'.mp h]
    · rw [hqq'.mpr h', h']
    · rw [h, h']
  have h2 := Nat.card_le_card_of_injective _ hinj
  have hB : Nat.card Bool = 2 := by simp
  omega

variable {G : Type} [Group G] [Finite G]

theorem card_mul_card_le_sq {R A : Subgroup G} {x : G} (hAR : A ≤ R)
    (hAc : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hsq : ∀ r ∈ R, r * r ∈ A) (hcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ A)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hx2 : x * x = 1) :
    Nat.card R * Nat.card A ≤
      (Nat.card (R ⊓ centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G)) ^ 2 := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  let Rx : Subgroup G :=
    { carrier := {r | r ∈ R ∧ x * r * x⁻¹ * r⁻¹ ∈ A}
      mul_mem' := fun {r s} hr hs => by
        refine ⟨mul_mem hr.1 hs.1, ?_⟩
        have e : x * (r * s) * x⁻¹ * (r * s)⁻¹ =
            (x * r * x⁻¹ * r⁻¹) * (r * (x * s * x⁻¹ * s⁻¹) * r⁻¹) := by group
        rw [e, show r * (x * s * x⁻¹ * s⁻¹) * r⁻¹ = x * s * x⁻¹ * s⁻¹ by
          rw [← hAc _ hs.2 r hr.1]; group]
        exact mul_mem hr.2 hs.2
      one_mem' := ⟨one_mem R, by simp⟩
      inv_mem' := fun {r} hr => by
        refine ⟨inv_mem hr.1, ?_⟩
        have e : x * r⁻¹ * x⁻¹ * r⁻¹⁻¹ = r⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * r := by group
        rw [e, show r⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * r = (x * r * x⁻¹ * r⁻¹)⁻¹ by
          rw [← hAc _ (inv_mem hr.2) r⁻¹ (inv_mem hr.1)]; group]
        exact inv_mem hr.2 }
  have hmemRx : ∀ r, r ∈ Rx ↔ r ∈ R ∧ x * r * x⁻¹ * r⁻¹ ∈ A := fun _ => Iff.rfl
  have hi : Nat.card Rx ≤ Nat.card (R ⊓ centralizer ({x} : Set G) : Subgroup G) *
      Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    let c : ↥Rx →* G :=
      { toFun := fun r => x * r * x⁻¹ * (r : G)⁻¹
        map_one' := by simp
        map_mul' := fun r s => by
          have hs := (hmemRx s).mp s.2
          have hr := (hmemRx r).mp r.2
          simp only [coe_mul]
          have e : x * (r * s : G) * x⁻¹ * (r * s : G)⁻¹ =
              (x * r * x⁻¹ * (r : G)⁻¹) * ((r : G) * (x * s * x⁻¹ * (s : G)⁻¹) * (r : G)⁻¹) := by
            group
          rw [e, show (r : G) * (x * s * x⁻¹ * (s : G)⁻¹) * (r : G)⁻¹ =
            x * s * x⁻¹ * (s : G)⁻¹ by rw [← hAc _ hs.2 r hr.1]; group] }
    have hc := Subgroup.card_ker_mul_card_range c
    have hker : Nat.card c.ker = Nat.card (R ⊓ centralizer ({x} : Set G) : Subgroup G) := by
      refine Nat.card_congr
        { toFun := fun r => ⟨r.1, mem_inf.mpr ⟨((hmemRx r.1).mp r.1.2).1,
            mem_centralizer_singleton_iff.mpr ?_⟩⟩
          invFun := fun r => ⟨⟨r.1, (hmemRx r.1).mpr ⟨(mem_inf.mp r.2).1, ?_⟩⟩, ?_⟩
          left_inv := fun r => rfl
          right_inv := fun r => rfl }
      · have h1 : x * r.1 * x⁻¹ * (r.1 : G)⁻¹ = 1 := r.2
        calc (r.1 : G) * x = x * r.1 * x⁻¹ * (r.1 : G)⁻¹ * r.1 * x := by rw [h1, one_mul]
          _ = x * r.1 := by group
      · have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp r.2).2
        rw [show x * r.1 * x⁻¹ * (r.1 : G)⁻¹ = 1 by rw [← h1]; group]
        exact one_mem A
      · show x * r.1 * x⁻¹ * (r.1 : G)⁻¹ = 1
        have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp r.2).2
        rw [← h1]
        group
    have hrange : c.range ≤ A ⊓ centralizer ({x} : Set G) := by
      rintro _ ⟨r, rfl⟩
      have hr := (hmemRx r).mp r.2
      refine mem_inf.mpr ⟨hr.2, mem_centralizer_singleton_iff.mpr ?_⟩
      show x * r * x⁻¹ * (r : G)⁻¹ * x = x * (x * r * x⁻¹ * (r : G)⁻¹)
      have h2 := hA2 _ hr.2
      calc x * r * x⁻¹ * (r : G)⁻¹ * x = (x * r * x⁻¹ * (r : G)⁻¹) * x := rfl
        _ = x * (x⁻¹ * (x * r * x⁻¹ * (r : G)⁻¹) * x) := by group
        _ = x * (x * r * x⁻¹ * (r : G)⁻¹) := by
          congr 1
          rw [hxinv]
          calc x * (x * r * x * (r : G)⁻¹) * x = (x * x) * r * x * (r : G)⁻¹ * x := by group
            _ = r * x * (r : G)⁻¹ * x := by rw [hx2, one_mul]
            _ = (x * r * x * (r : G)⁻¹)⁻¹ := by
              simp only [mul_inv_rev, inv_inv, hxinv, mul_assoc]
            _ = x * r * x * (r : G)⁻¹ := by
              rw [inv_eq_of_mul_eq_one_right (by rw [hxinv] at h2; exact h2)]
    have h3 := card_le_of_le hrange
    rw [← hc, hker]
    exact Nat.mul_le_mul_left _ h3
  have hii : Nat.card R * Nat.card A ≤ Nat.card Rx ^ 2 := by
    set N : Subgroup R := A.subgroupOf R with hNdef
    have hN : N.Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simp only [coe_mul, coe_inv]
      rw [show (g : G) * n * (g : G)⁻¹ = n by rw [← hAc _ hn g g.2]; group]
      exact hn⟩
    let σ : R →* R :=
      { toFun := fun r => ⟨x * r * x⁻¹, hxR r r.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun r s => Subtype.ext (by simp only [coe_mul]; group) }
    have hσN : N ≤ N.comap σ := fun n hn => by
      rw [mem_comap, mem_subgroupOf]
      exact hxA _ (mem_subgroupOf.mp hn)
    let σb : R ⧸ N →* R ⧸ N := QuotientGroup.map N N σ hσN
    have hσb : ∀ r : R, σb (QuotientGroup.mk r) = QuotientGroup.mk (σ r) := fun _ => rfl
    have hmk : ∀ r s : R, (QuotientGroup.mk r : R ⧸ N) = QuotientGroup.mk s ↔
        (r : G)⁻¹ * s ∈ A := fun r s => by
      rw [QuotientGroup.eq, mem_subgroupOf]
      rfl
    have hWcomm : ∀ u v : R ⧸ N, u * v = v * u := by
      intro u v
      induction u using QuotientGroup.induction_on with
      | H r =>
      induction v using QuotientGroup.induction_on with
      | H s =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
      simp only [coe_mul, mul_inv_rev]
      have := hcomm _ (inv_mem s.2) _ (inv_mem r.2)
      rw [show (s : G)⁻¹ * (r : G)⁻¹ * (s * r) = (s : G)⁻¹ * (r : G)⁻¹ * (s : G)⁻¹⁻¹ * (r : G)⁻¹⁻¹
        by group]
      exact this
    have hσσ : ∀ u : R ⧸ N, σb (σb u) = u := by
      intro u
      induction u using QuotientGroup.induction_on with
      | H r =>
      rw [hσb, hσb]
      congr 1
      apply Subtype.ext
      show x * (x * r * x⁻¹) * x⁻¹ = r
      rw [hxinv]
      calc x * (x * r * x) * x = (x * x) * r * (x * x) := by group
        _ = r := by rw [hx2, one_mul, mul_one]
    let ψ : R ⧸ N →* R ⧸ N :=
      { toFun := fun u => u * σb u
        map_one' := by rw [map_one, one_mul]
        map_mul' := fun u v => by
          rw [map_mul]
          calc u * v * (σb u * σb v) = u * (v * σb u) * σb v := by group
            _ = u * (σb u * v) * σb v := by rw [hWcomm v]
            _ = u * σb u * (v * σb v) := by group }
    have hrange : ψ.range ≤ ψ.ker := by
      rintro _ ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      show u * σb u * σb (u * σb u) = 1
      rw [map_mul, hσσ]
      have h2 : ∀ w : R ⧸ N, w * w = 1 := fun w => by
        induction w using QuotientGroup.induction_on with
        | H r =>
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact hsq r r.2
      calc u * σb u * (σb u * u) = u * (σb u * σb u) * u := by group
        _ = 1 := by rw [h2, mul_one, h2]
    let Φ : R →* R ⧸ N := ψ.comp (QuotientGroup.mk' N)
    have hΦrange : Φ.range = ψ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
        ← MonoidHom.range_eq_map]
    have hΦker : Nat.card Φ.ker = Nat.card Rx := by
      have hle : Rx ≤ R := fun r hr => ((hmemRx r).mp hr).1
      have hkeq : Φ.ker = Rx.subgroupOf R := by
        ext r
        rw [MonoidHom.mem_ker, mem_subgroupOf, hmemRx]
        show (QuotientGroup.mk r : R ⧸ N) * σb (QuotientGroup.mk r) = 1 ↔ _
        rw [hσb, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
        show (r : G) * (x * r * x⁻¹) ∈ A ↔ _
        have hr2 := hsq r r.2
        constructor
        · intro h1
          refine ⟨r.2, ?_⟩
          have e : x * r * x⁻¹ * (r : G)⁻¹ = ((r : G) * (x * r * x⁻¹)) * ((r : G) * r)⁻¹ := by
            calc x * r * x⁻¹ * (r : G)⁻¹ =
                (r : G)⁻¹ * ((r : G) * (x * r * x⁻¹)) * (r : G)⁻¹ := by group
              _ = ((r : G) * (x * r * x⁻¹)) * (r : G)⁻¹ * (r : G)⁻¹ := by
                rw [hAc _ h1 _ (inv_mem r.2)]
              _ = _ := by group
          rw [e]
          exact mul_mem h1 (inv_mem hr2)
        · rintro ⟨-, h⟩
          have e : (r : G) * (x * r * x⁻¹) = (x * r * x⁻¹ * (r : G)⁻¹) * ((r : G) * r) := by
            calc (r : G) * (x * r * x⁻¹) = (r : G) * (x * r * x⁻¹ * (r : G)⁻¹) * r := by group
              _ = (x * r * x⁻¹ * (r : G)⁻¹) * r * r := by rw [hAc _ h _ r.2]
              _ = _ := by group
          rw [e]
          exact mul_mem h hr2
      rw [hkeq]
      exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
    have h1 := Subgroup.card_ker_mul_card_range Φ
    have h2 := Subgroup.card_ker_mul_card_range ψ
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hNA : Nat.card N = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv
    have h4 := card_le_of_le hrange
    rw [hΦrange, hΦker] at h1
    rw [hNA] at h3
    have hP : 0 < Nat.card ψ.range := Nat.card_pos
    have hK : Nat.card Rx = Nat.card ψ.ker * Nat.card A := by
      apply Nat.eq_of_mul_eq_mul_right hP
      rw [h1, h3, ← h2]
      ring
    calc Nat.card R * Nat.card A = Nat.card Rx * Nat.card ψ.range * Nat.card A := by rw [h1]
      _ ≤ Nat.card Rx * Nat.card ψ.ker * Nat.card A := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ h4
      _ = Nat.card Rx ^ 2 := by rw [sq, hK]; ring
  exact hii.trans (Nat.pow_le_pow_left hi 2)

omit [Finite G] in
theorem mem_map_conj_iff_conj_mem {F : Subgroup G} {g y : G} :
    y ∈ F.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ F := by
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    exact ⟨_, h, by group⟩

omit [Finite G] in
theorem isElemAbelian_map_mulAutConj {F : Subgroup G} (hF : IsElemAbelian 2 F) (g : G) :
    IsElemAbelian 2 (F.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨a', ha', ha'e⟩ := mem_map.mp a.2
    obtain ⟨b', hb', hb'e⟩ := mem_map.mp b.2
    have hc' : a' * b' = b' * a' := congrArg Subtype.val (hF.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    show (a : G) * b = b * a
    rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, hc']
  · obtain ⟨a, ha, rfl⟩ := mem_map.mp hy
    rw [← map_pow, hF.2 a ha, map_one]

omit [Finite G] in
theorem isElemAbelian_sup_of_forall_commute {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B : Subgroup G) := by
  have hBN : B ≤ normalizer (A : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => hAB a ha b hb)
  have hdecomp : ∀ z ∈ A ⊔ B, ∃ b ∈ B, ∃ a ∈ A, b * a = z := fun z hz =>
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hBN (by rwa [sup_comm] at hz)
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  refine ⟨⟨⟨fun z w => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨b, hb, a, ha, hz⟩ := hdecomp z z.2
    obtain ⟨b', hb', a', ha', hw⟩ := hdecomp w w.2
    show (z : G) * w = w * z
    rw [← hz, ← hw]
    calc b * a * (b' * a') = b * (a * b') * a' := by group
      _ = b * (b' * a) * a' := by rw [hAB a ha b' hb']
      _ = (b * b') * (a * a') := by group
      _ = (b' * b) * (a' * a) := by rw [hBc b hb b' hb', hAc a ha a' ha']
      _ = b' * (b * a') * a := by group
      _ = b' * (a' * b) * a := by rw [hAB a' ha' b hb]
      _ = b' * a' * (b * a) := by group
  · obtain ⟨b, hb, a, ha, rfl⟩ := hdecomp z hz
    calc (b * a) ^ 2 = b * (a * b) * a := by rw [sq]; group
      _ = b * (b * a) * a := by rw [hAB a ha b hb]
      _ = b ^ 2 * a ^ 2 := by rw [sq, sq]; group
      _ = 1 := by rw [hB.2 b hb, hA.2 a ha, one_mul]

section D

variable {F : Subgroup G}

omit [Finite G] in
theorem centralizer_le_normalizer_of_trans
    (htrans : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (F : Set G), n * a * n⁻¹ = b)
    {f : G} (hf : f ∈ F) (hf1 : f ≠ 1)
    (hCf : centralizer ({f} : Set G) ≤ normalizer (F : Set G)) :
    ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G) := by
  intro a ha ha1 z hz
  obtain ⟨n, hn, hna⟩ := htrans f hf a ha hf1 ha1
  have h1 : n⁻¹ * z * n ∈ centralizer ({f} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hz ⊢
    calc n⁻¹ * z * n * f = n⁻¹ * (z * (n * f * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * f * n⁻¹) * z) * n := by rw [hna, hz]
      _ = f * (n⁻¹ * z * n) := by group
  rw [show z = n * (n⁻¹ * z * n) * n⁻¹ by group]
  exact mul_mem (mul_mem hn (hCf h1)) (inv_mem hn)

theorem false_of_conj_mem_of_mem_normalizer (hFel : IsElemAbelian 2 F) (hF8 : Nat.card F = 8)
    (htrans : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (F : Set G), n * a * n⁻¹ = b)
    (hstar : ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G))
    (hE64 : ∀ P : Subgroup G, P ≤ centralizer (F : Set G) → IsElemAbelian 2 P → Nat.card P ≤ 32)
    (hR : Nat.card (centralizer (F : Set G)) = 2 ^ 11)
    (hsq : ∀ r ∈ centralizer (F : Set G), r ^ 2 ∈ F)
    (hcomm : ∀ r ∈ centralizer (F : Set G), ∀ r' ∈ centralizer (F : Set G),
      r * r' * r⁻¹ * r'⁻¹ ∈ F)
    {x g : G} (hxN : x ∈ normalizer (F : Set G)) (hxR : x ∉ centralizer (F : Set G))
    (hxg : g⁻¹ * x * g ∈ F) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := centralizer (F : Set G) with hRdef
  set B : Subgroup G := F.map (MulAut.conj g).toMonoidHom with hBdef
  have hBel : IsElemAbelian 2 B := isElemAbelian_map_mulAutConj hFel g
  have hB8 : Nat.card B = 8 := by
    rw [hBdef, card_map_of_injective (MulAut.conj g).injective, hF8]
  have hFc : ∀ a ∈ F, ∀ a' ∈ F, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hFel.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hFR : F ≤ R := fun a ha => mem_centralizer_iff.mpr fun a' ha' => hFc a' ha' a ha
  have hRF : ∀ r ∈ R, ∀ a ∈ F, a * r = r * a := fun r hr a ha => mem_centralizer_iff.mp hr a ha
  have hx1 : x ≠ 1 := fun h => hxR (h ▸ one_mem R)
  have hxB : x ∈ B := mem_map_conj_iff_conj_mem.mpr hxg
  have hx2 : x * x = 1 := by
    have h := hBel.2 x hxB
    rwa [sq] at h
  have h1 : ∀ a ∈ F, a ∈ centralizer (B : Set G) → a = 1 := by
    intro a ha haB
    by_contra ha1
    have hBN : B ≤ normalizer (F : Set G) := fun b hb =>
      hstar a ha ha1 (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haB b hb))
    obtain ⟨b, hbB, hb1, hbR⟩ := exists_mem_centralizer_of_le_normalizer hFel hF8 hBN
      (fun p hp => hBel.2 p hp) (by rw [hB8]; norm_num)
    have hbg : g⁻¹ * b * g ∈ F := mem_map_conj_iff_conj_mem.mp hbB
    by_cases hbF : b ∈ F
    · have hgN := mem_normalizer_of_conj_mem_star htrans hstar hbF hbg hb1
      apply hxR
      apply hFR
      rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group]
      exact (mem_normalizer_iff.mp hgN _).mp hxg
    · exact false_of_conj_mem_of_mem_centralizer hFel hF8 htrans hstar hE64 hbR hbF hbg
  have hCx : centralizer ({x} : Set G) ≤ normalizer (B : Set G) :=
    centralizer_le_normalizer_conj hstar hxg hx1
  have hxF : ∀ a ∈ F, x * a * x⁻¹ ∈ F := fun a ha => (mem_normalizer_iff.mp hxN a).mp ha
  have hxF' : ∀ a ∈ F, x⁻¹ * a * x ∈ F := fun a ha => by
    have := (mem_normalizer_iff.mp (inv_mem hxN) a).mp ha
    simpa using this
  have hxR' : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr => mem_centralizer_iff.mpr fun a ha => by
    have h := hRF r hr _ (hxF' a ha)
    calc a * (x * r * x⁻¹) = x * ((x⁻¹ * a * x) * r) * x⁻¹ := by group
      _ = x * (r * (x⁻¹ * a * x)) * x⁻¹ := by rw [h]
      _ = x * r * x⁻¹ * a := by group
  set F₀ := F ⊓ centralizer ({x} : Set G) with hF₀def
  have hF₀ : Nat.card F₀ = 4 := by
    have h := card_mul_card_le_sq (R := F) (A := ⊥) (x := x) bot_le
      (fun a ha r _ => by rw [mem_bot.mp ha, one_mul, mul_one])
      (fun a ha => by rw [mem_bot.mp ha, one_mul])
      (fun r hr => by rw [mem_bot, ← sq]; exact hFel.2 r hr)
      (fun r hr r' hr' => by rw [mem_bot, hFc r hr r' hr']; group)
      hxF (fun a ha => by rw [mem_bot.mp ha, mul_one, mul_inv_cancel]; exact one_mem _) hx2
    rw [bot_inf_eq, card_bot, mul_one, mul_one, hF8] at h
    have hdvd : Nat.card F₀ ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hF8]
      exact card_dvd_of_le inf_le_left
    have hne : Nat.card F₀ ≠ 8 := by
      intro h8
      apply hxR
      have hle : F ≤ F₀ := (eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hF8, h8]))).ge
      exact mem_centralizer_iff.mpr fun a ha =>
        mem_centralizer_singleton_iff.mp (mem_inf.mp (hle ha)).2
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hi'] at h hne ⊢
    revert h hne
    interval_cases i <;> norm_num
  set K := R ⊓ centralizer ({x} : Set G) with hKdef
  have hK : 32 ≤ Nat.card K := by
    have h := card_mul_card_le_sq (R := R) (A := F) (x := x) hFR
      (fun a ha r hr => hRF r hr a ha) (fun a ha => by rw [← sq]; exact hFel.2 a ha)
      (fun r hr => by rw [← sq]; exact hsq r hr) hcomm hxR' hxF hx2
    rw [hR, hF8, hF₀] at h
    by_contra hlt
    have h31 : Nat.card K ≤ 31 := by omega
    have := Nat.mul_le_mul h31 h31
    nlinarith
  obtain ⟨e⟩ := GHarris.nonempty_mulAut_equiv_GL32 hBel hB8
  set Nb := normalizer (B : Set G) with hNbdef
  set ψ : ↥Nb →* GL (Fin 3) (ZMod 2) := e.toMonoidHom.comp B.normalizerMonoidHom with hψdef
  have hψ : ∀ n : Nb, ψ n = 1 → (n : G) ∈ centralizer (B : Set G) := by
    intro n hn
    have h2 : B.normalizerMonoidHom n = 1 := by
      apply e.injective
      rw [map_one]
      exact hn
    rw [mem_centralizer_iff]
    intro b hb
    have h3 := congrArg (fun φ : MulAut B => ((φ ⟨b, hb⟩ : B) : G)) h2
    simp only [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
    calc b * (n : G) = (n : G) * b * (n : G)⁻¹ * n := by rw [h3]
      _ = (n : G) * b := by group
  have hKNb : K ≤ Nb := fun k hk => hCx (mem_inf.mp hk).2
  have hF₀Nb : F₀ ≤ Nb := fun a ha => hCx (mem_inf.mp ha).2
  set φ : ↥K →* GL (Fin 3) (ZMod 2) := ψ.comp (inclusion hKNb) with hφdef
  set χ : ↥F₀ →* GL (Fin 3) (ZMod 2) := ψ.comp (inclusion hF₀Nb) with hχdef
  have hχ : Function.Injective χ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [mem_bot]
    apply Subtype.ext
    exact h1 a (mem_inf.mp a.2).1 (hψ (inclusion hF₀Nb a) (MonoidHom.mem_ker.mp ha))
  have hQ4 : Nat.card χ.range = 4 := by
    rw [← hF₀]
    exact (Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv).symm
  have hKp : IsPGroup 2 K := (IsPGroup.of_card hR).to_le inf_le_left
  have hP : IsPGroup 2 φ.range := hKp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hPcard : Nat.card φ.range ≤ 4 := by
    refine card_le_four_of_commute_GL32 hP ?_ (by rw [hQ4]; norm_num) ?_
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (hFel.2 a (mem_inf.mp a.2).1), map_one]
    ·
      rintro _ ⟨k, rfl⟩ _ ⟨a, rfl⟩
      have hka : (k : G) * a = a * k := (hRF k (mem_inf.mp k.2).1 a (mem_inf.mp a.2).1).symm
      show ψ (inclusion hKNb k) * ψ (inclusion hF₀Nb a) =
        ψ (inclusion hF₀Nb a) * ψ (inclusion hKNb k)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hka
  set Y : Subgroup G := φ.ker.map K.subtype with hYdef
  have hY8 : 8 ≤ Nat.card Y := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hYdef, card_map_of_injective K.subtype_injective]
    by_contra hlt
    have h7 : Nat.card φ.ker ≤ 7 := by omega
    have := Nat.mul_le_mul h7 hPcard
    linarith
  have hYmem : ∀ y ∈ Y, y ∈ R ∧ y ∈ centralizer (B : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨(mem_inf.mp k.2).1, hψ (inclusion hKNb k) hk⟩
  have hYF : ∀ y ∈ Y, y ∈ F → y = 1 := fun y hy hyF => h1 y hyF (hYmem y hy).2
  have hYel : IsElemAbelian 2 Y := by
    refine ⟨⟨⟨fun y y' => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · have hc := hYF _ (mul_mem (mul_mem (mul_mem y.2 y'.2) (inv_mem y.2)) (inv_mem y'.2))
        (hcomm _ (hYmem _ y.2).1 _ (hYmem _ y'.2).1)
      show (y : G) * y' = y' * y
      calc (y : G) * y' = (y : G) * y' * (y : G)⁻¹ * (y' : G)⁻¹ * (y' * y) := by group
        _ = y' * y := by rw [hc, one_mul]
    · exact hYF _ (pow_mem hy 2) (hsq y (hYmem y hy).1)
  have hFY : F ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact mem_bot.mpr (hYF z (mem_inf.mp hz).2 (mem_inf.mp hz).1)
  have hYN : Y ≤ normalizer (F : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (hYmem y hy).1
  have hcard := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hYN
  rw [hFY, card_bot, mul_one, hF8] at hcard
  have hle := hE64 (F ⊔ Y) (sup_le hFR fun y hy => (hYmem y hy).1)
    (isElemAbelian_sup_of_forall_commute hFel hYel fun a ha y hy => hRF y (hYmem y hy).1 a ha)
  omega

theorem mem_of_conj_mem_of_mem_normalizer (hFel : IsElemAbelian 2 F) (hF8 : Nat.card F = 8)
    (htrans : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (F : Set G), n * a * n⁻¹ = b)
    (hstar : ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G))
    (hE64 : ∀ P : Subgroup G, P ≤ centralizer (F : Set G) → IsElemAbelian 2 P → Nat.card P ≤ 32)
    (hR : Nat.card (centralizer (F : Set G)) = 2 ^ 11)
    (hsq : ∀ r ∈ centralizer (F : Set G), r ^ 2 ∈ F)
    (hcomm : ∀ r ∈ centralizer (F : Set G), ∀ r' ∈ centralizer (F : Set G),
      r * r' * r⁻¹ * r'⁻¹ ∈ F)
    {v g : G} (hvN : v ∈ normalizer (F : Set G)) (hvg : g⁻¹ * v * g ∈ F) : v ∈ F := by
  by_cases hvR : v ∈ centralizer (F : Set G)
  · by_contra hvF
    exact false_of_conj_mem_of_mem_centralizer hFel hF8 htrans hstar hE64 hvR hvF hvg
  · exact (false_of_conj_mem_of_mem_normalizer hFel hF8 htrans hstar hE64 hR hsq hcomm hvN hvR
      hvg).elim

theorem exists_sylow_le_normalizer_of_forall (hFp : IsPGroup 2 F)
    (hcl : ∀ v ∈ normalizer (F : Set G), ∀ g : G, g⁻¹ * v * g ∈ F → v ∈ F) :
    ∃ S : Sylow 2 G, F ≤ S ∧ (S : Subgroup G) ≤ normalizer (F : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hFS⟩ := hFp.exists_le_sylow
  refine ⟨S, hFS, ?_⟩
  set V : Subgroup G := (S : Subgroup G) ⊓ normalizer (F : Set G) with hVdef
  have hFV : F ≤ V := le_inf hFS Subgroup.le_normalizer
  by_contra hSV
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : V.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hSV fun s hs => ?_
    have hs' : (⟨s, hs⟩ : (S : Subgroup G)) ∈ V.subgroupOf S := htop ▸ mem_top _
    exact (mem_inf.mp (mem_subgroupOf.mp hs')).2
  obtain ⟨u, huN, huV⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq (inf_le_left : V ≤ S)] at huN
  have huN' : (u : G) ∈ normalizer (V : Set G) := mem_subgroupOf.mp huN
  apply huV
  refine mem_subgroupOf.mpr (mem_inf.mpr ⟨u.2, mem_normalizer_fintype fun a ha => ?_⟩)
  have hv : (u : G) * a * (u : G)⁻¹ ∈ V := (mem_normalizer_iff.mp huN' a).mp (hFV ha)
  refine hcl _ (mem_inf.mp hv).2 u ?_
  rw [show (u : G)⁻¹ * (u * a * (u : G)⁻¹) * u = a by group]
  exact ha

theorem false_of_centralizer_le_normalizer_of_card (h34 : NoStronglyClosedAbelian G)
    (hFel : IsElemAbelian 2 F) (hF8 : Nat.card F = 8)
    (htrans : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → ∃ n ∈ normalizer (F : Set G), n * a * n⁻¹ = b)
    (hstar : ∀ a ∈ F, a ≠ 1 → centralizer ({a} : Set G) ≤ normalizer (F : Set G))
    (hE64 : ∀ P : Subgroup G, P ≤ centralizer (F : Set G) → IsElemAbelian 2 P → Nat.card P ≤ 32)
    (hR : Nat.card (centralizer (F : Set G)) = 2 ^ 11)
    (hsq : ∀ r ∈ centralizer (F : Set G), r ^ 2 ∈ F)
    (hcomm : ∀ r ∈ centralizer (F : Set G), ∀ r' ∈ centralizer (F : Set G),
      r * r' * r⁻¹ * r'⁻¹ ∈ F) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  obtain ⟨S, hFS, hSN⟩ := exists_sylow_le_normalizer_of_forall hFp fun v hv g hg =>
    mem_of_conj_mem_of_mem_normalizer hFel hF8 htrans hstar hE64 hR hsq hcomm hv hg
  exact false_of_centralizer_le_normalizer_of_sylow h34 hFel hF8 htrans hstar hE64 S hFS
    fun v hv hvR g hg => false_of_conj_mem_of_mem_normalizer hFel hF8 htrans hstar hE64 hR hsq
      hcomm (hSN hv) hvR (g := g⁻¹) (by rwa [inv_inv])

end D

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {y d : G}

theorem not_centralizer_le_normalizer_of_card
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hC : centralizer (gmsA L T : Set G) = R)
    (hE64 : ∀ P : Subgroup G, P ≤ R → IsElemAbelian 2 P → Nat.card P ≤ 32) {f : G}
    (hf : f ∈ gmsA L T) (hf1 : f ≠ 1) :
    ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G) := by
  intro hCf
  obtain ⟨hAel, hA8⟩ := hS.isElemAbelian_gmsA_and_card
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  have htrans : ∀ a ∈ gmsA L T, ∀ b ∈ gmsA L T, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ normalizer (gmsA L T : Set G), n * a * n⁻¹ = b := fun _ ha _ hb ha1 hb1 =>
    hS.exists_conj_eq_of_mem_gmsA hR₂ ha hb ha1 hb1
  have hR : Nat.card (centralizer (gmsA L T : Set G)) = 2 ^ 11 := by
    rw [hC, hS.card_R hR₂, card_T_eq hS h4]
    norm_num
  rw [← hC] at hE64
  refine false_of_centralizer_le_normalizer_of_card h34 hAel hA8 htrans
    (centralizer_le_normalizer_of_trans htrans hf hf1 hCf) hE64 hR
    (fun r hr => hS.sq_mem_gmsA_of_mem_R h34 hX (hC ▸ hr))
    (fun r hr r' hr' => hS.commutator_mem_gmsA h34 (hC ▸ hr) (hC ▸ hr'))

theorem not_centralizer_le_normalizer_of_not_isSylowOf
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hC : centralizer (gmsA L T : Set G) = R) (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G)))
    {f : G} (hf : f ∈ gmsA L T) (hf1 : f ≠ 1) :
    ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G) :=
  hS.not_centralizer_le_normalizer_of_card h34 hR₂ h4 hC
    (hS.card_le_of_isElemAbelian h34 hR₂ h4 hNS) hf hf1

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
