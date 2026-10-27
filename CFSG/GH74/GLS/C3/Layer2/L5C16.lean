module

public import CFSG.GH74.GLS.C3.Layer2.L5C15
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Class1

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} {S₁ : Subgroup G} {hS : c.S1Data S₁}

theorem Coord5.class1_normalizer_R
    (hAut : ∀ γ : ↥Sh1 ≃* ↥Sh1, ∀ r : ↥Sh1, (r : Perm (Fin 16)) ∈ RsubP1 →
      ((γ r : ↥Sh1) : Perm (Fin 16)) ∈ RsubP1)
    (Ψ : c.ModelIso hS Sh1 tr1 yHat1) {b : G} (hb : b ∈ normalizer (S₁ : Set G)) :
    b ∈ normalizer ((c.lift Rm : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_le fun r hr => ?_
  have hrS : r ∈ S₁ := Coord5.R_le_S1 hS hr
  have hbr : b * r * b⁻¹ ∈ S₁ := (mem_normalizer_iff.1 hb r).1 hrS
  obtain ⟨i, hi⟩ := (Ψ.mem_R hrS).1 hr
  have hrm : ((Ψ.ψ ⟨r, hrS⟩ : ↥Sh1) : Perm (Fin 16)) ∈ RsubP1 := by
    rw [hi, mem_RsubP1]
    exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩
  let γ : ↥Sh1 ≃* ↥Sh1 := Ψ.ψ.symm.trans ((conjAutOfNormalizer hb).trans Ψ.ψ)
  have h1 := hAut γ (Ψ.ψ ⟨r, hrS⟩) hrm
  have h2 : γ (Ψ.ψ ⟨r, hrS⟩) = Ψ.ψ ⟨b * r * b⁻¹, hbr⟩ := by
    show Ψ.ψ (conjAutOfNormalizer hb (Ψ.ψ.symm (Ψ.ψ ⟨r, hrS⟩))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [h2, mem_RsubP1] at h1
  obtain ⟨j, -, hj⟩ := List.mem_map.1 h1
  exact (Ψ.mem_R hbr).2 ⟨j, hj.symm⟩

theorem Coord5.class1_weak
    (hE16 : ∀ B : Subgroup (Perm (Fin 16)), B ≤ Sh1 → Nat.card B = 16 → (∀ b ∈ B, b * b = 1) →
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → B = RsubP1)
    (Ψ : c.ModelIso hS Sh1 tr1 yHat1) (g : G)
    (hg : (c.lift Rm).map (MulAut.conj g).toMonoidHom ≤ S₁) :
    (c.lift Rm).map (MulAut.conj g).toMonoidHom = c.lift Rm := by
  set R := c.lift Rm with hR
  set A' := R.map (MulAut.conj g).toMonoidHom with hA'
  have hmemA' : ∀ y, y ∈ A' ↔ ∃ r ∈ R, g * r * g⁻¹ = y := by
    intro y
    rw [hA', Subgroup.mem_map]
    simp [MulAut.conj_apply]
  have hsq : ∀ y ∈ A', y * y = 1 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := (hmemA' y).1 hy
    have := Coord5.lift_sq (c := c) (M := Rm) (fun p hp => Rm_sq p hp) hr
    calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hcomm : ∀ y ∈ A', ∀ y' ∈ A', y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨r, hr, rfl⟩ := (hmemA' y).1 hy
    obtain ⟨r', hr', rfl⟩ := (hmemA' y').1 hy'
    have := Coord5.lift_comm (c := c) (M := Rm) (fun p hp q hq => Rm_comm p hp q hq) hr hr'
    calc g * r * g⁻¹ * (g * r' * g⁻¹) = g * (r * r') * g⁻¹ := by group
      _ = g * (r' * r) * g⁻¹ := by rw [this]
      _ = g * r' * g⁻¹ * (g * r * g⁻¹) := by group
  let f : ↥S₁ →* Perm (Fin 16) := Sh1.subtype.comp Ψ.ψ.toMonoidHom
  have hfinj : Function.Injective f := fun s t hst => Ψ.ψ.injective (Subtype.ext hst)
  set B : Subgroup (Perm (Fin 16)) := (A'.subgroupOf S₁).map f with hB
  have hmemB : ∀ b, b ∈ B ↔ ∃ y : ↥S₁, (y : G) ∈ A' ∧ f y = b := by
    intro b
    rw [hB, Subgroup.mem_map]
    simp [Subgroup.mem_subgroupOf]
  have hBle : B ≤ Sh1 := by
    intro b hb
    obtain ⟨y, -, rfl⟩ := (hmemB b).1 hb
    exact (Ψ.ψ y).2
  have hcardA' : Nat.card A' = 16 := by
    rw [hA', Subgroup.card_map_of_injective (fun u v huv => (MulAut.conj g).injective huv)]
    exact Coord5.card_lift_Rm (c := c)
  have hcardB : Nat.card B = 16 := by
    rw [hB, Subgroup.card_map_of_injective hfinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv, hcardA']
  have hBeq : B = RsubP1 := hE16 B hBle hcardB
    (by
      intro b hb
      obtain ⟨y, hy, rfl⟩ := (hmemB b).1 hb
      rw [← map_mul]
      have : y * y = 1 := Subtype.ext (hsq y hy)
      rw [this, map_one])
    (by
      intro b hb b' hb'
      obtain ⟨y, hy, rfl⟩ := (hmemB b).1 hb
      obtain ⟨y', hy', rfl⟩ := (hmemB b').1 hb'
      rw [← map_mul, ← map_mul]
      have : y * y' = y' * y := Subtype.ext (hcomm y hy y' hy')
      rw [this])
  have hle : A' ≤ R := by
    intro y hy
    have hyS : y ∈ S₁ := hg hy
    have hmem : f ⟨y, hyS⟩ ∈ B := (hmemB _).2 ⟨⟨y, hyS⟩, hy, rfl⟩
    rw [hBeq, mem_RsubP1] at hmem
    obtain ⟨j, -, hj⟩ := List.mem_map.1 hmem
    exact (Ψ.mem_R hyS).2 ⟨j, hj.symm⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA', Coord5.card_lift_Rm (c := c)])

theorem Coord5.class1_rho_mem
    (hF : C1Facts2) (hRed : c.Red)
    (hNo : ¬ ∃ γ : ↥S0subP1 ≃* ↥S0subP1, ∀ (s : ↥S0subP1) (i : Fin 16),
      (s : Perm (Fin 16)) = tr1 i → ((γ s : ↥S0subP1) : Perm (Fin 16)) = tr1 (cHat i))
    (Ψ : c.ModelIso hS Sh1 tr1 yHat1) (n : ↥c.N) : c.rhoG n ∈ n24L := by
  by_contra hn
  have hcH : cHat ∈ c.rhoG.range := by
    apply hF.cHat_gen c.rhoG.range
    · rintro m ⟨n', rfl⟩
      exact ⟨(Coord5.rho_stable hRed n').1, hRed.pres n', (Coord5.rho_stable hRed n').2⟩
    · intro A hA
      obtain ⟨n', hn'⟩ := hRed.nbar A hA
      exact ⟨n', hn'⟩
    · exact ⟨c.rhoG n, ⟨n, rfl⟩, hn⟩
  obtain ⟨n₁, hn₁⟩ := hcH
  have hov : ∀ (s : G) (hs : s ∈ S₁), ((Ψ.ψ ⟨s, hs⟩ : ↥Sh1) : Perm (Fin 16)) ∈ S0subP1 ↔
      c.rhoG ⟨s, hS.hN hs⟩ ∈ v4L := by
    intro s hs
    rw [mem_S0subP1]
    unfold S0L1
    rw [List.mem_filter]
    have hmem : ((Ψ.ψ ⟨s, hs⟩ : ↥Sh1) : Perm (Fin 16)) ∈ Sh1L := mem_Sh1.1 (Ψ.ψ ⟨s, hs⟩).2
    simp only [hmem, true_and]
    unfold overV4
    simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_finRange,
      true_implies]
    constructor
    · rintro ⟨d, hd, hdi⟩
      have : d = c.rhoG ⟨s, hS.hN hs⟩ :=
        Equiv.ext fun i => by rw [hdi i, Ψ.rhoF_eq Glue.tr1_injective hs i]
      rw [← this]
      exact hd
    · intro hmem2
      exact ⟨_, hmem2, fun i => by rw [Ψ.rhoF_eq Glue.tr1_injective hs i]⟩
  have hconj : ∀ (s : G) (hs : s ∈ S₁), c.rhoG ⟨s, hS.hN hs⟩ ∈ v4L →
      ∃ ht : n₁.1 * s * n₁.1⁻¹ ∈ S₁, c.rhoG ⟨n₁.1 * s * n₁.1⁻¹, hS.hN ht⟩ ∈ v4L := by
    intro s hs hv
    have htN : n₁.1 * s * n₁.1⁻¹ ∈ c.N := mul_mem (mul_mem n₁.2 (hS.hN hs)) (inv_mem n₁.2)
    have hρt : c.rhoG ⟨n₁.1 * s * n₁.1⁻¹, htN⟩ = cHat * c.rhoG ⟨s, hS.hN hs⟩ * cHat⁻¹ := by
      have : (⟨n₁.1 * s * n₁.1⁻¹, htN⟩ : ↥c.N) = n₁ * ⟨s, hS.hN hs⟩ * n₁⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hn₁]
    have hv4 : c.rhoG ⟨n₁.1 * s * n₁.1⁻¹, htN⟩ ∈ v4L := by
      rw [hρt]
      exact hF.cHat_v4 _ hv
    have htS : n₁.1 * s * n₁.1⁻¹ ∈ S₁ := Coord5.mem_S1_of_rho hS htN (hF.v4_sub_d8 _ hv4)
    exact ⟨htS, hv4⟩
  let e : ↥S0subP1 →* ↥S₁ := Ψ.ψ.symm.toMonoidHom.comp (Subgroup.inclusion Glue.S0subP1_le_Sh1)
  have he : ∀ m : ↥S0subP1, Ψ.ψ (e m) = Subgroup.inclusion Glue.S0subP1_le_Sh1 m := fun m => by
    simp [e]
  have hein : Function.Injective e := fun m m' hmm' => by
    have h1 : Subgroup.inclusion Glue.S0subP1_le_Sh1 m = Subgroup.inclusion Glue.S0subP1_le_Sh1 m' := by
      rw [← he m, ← he m', hmm']
    exact Subgroup.inclusion_injective _ h1
  have hev : ∀ m : ↥S0subP1, c.rhoG ⟨(e m : G), hS.hN (e m).2⟩ ∈ v4L := by
    intro m
    have hm : ((Ψ.ψ ⟨(e m : G), (e m).2⟩ : ↥Sh1) : Perm (Fin 16)) ∈ S0subP1 := by
      have h1 : (⟨(e m : G), (e m).2⟩ : ↥S₁) = e m := rfl
      rw [h1, he m, Subgroup.coe_inclusion]
      exact m.2
    exact (hov _ (e m).2).1 hm
  obtain ⟨Dfun, hDfun⟩ : ∃ D : ↥S0subP1 → ↥S₁, ∀ m, (D m : G) = n₁.1 * (e m : G) * n₁.1⁻¹ :=
    ⟨fun m => ⟨n₁.1 * (e m : G) * n₁.1⁻¹, (hconj (e m) (e m).2 (hev m)).1⟩, fun m => rfl⟩
  have hD_mul : ∀ m m' : ↥S0subP1, Dfun (m * m') = Dfun m * Dfun m' := fun m m' => by
    apply Subtype.ext
    rw [hDfun, Subgroup.coe_mul, hDfun, hDfun, map_mul, Subgroup.coe_mul]
    group
  have hDmem : ∀ m : ↥S0subP1, ((Ψ.ψ (Dfun m) : ↥Sh1) : Perm (Fin 16)) ∈ S0subP1 := fun m => by
    have h1 := hconj (e m) (e m).2 (hev m)
    have h2 : Dfun m = ⟨n₁.1 * (e m : G) * n₁.1⁻¹, h1.1⟩ := Subtype.ext (hDfun m)
    rw [h2]
    exact (hov _ h1.1).2 h1.2
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥S0subP1 →* ↥S0subP1, ∀ m,
      ((γ m : ↥S0subP1) : Perm (Fin 16)) = ((Ψ.ψ (Dfun m) : ↥Sh1) : Perm (Fin 16)) :=
    ⟨MonoidHom.mk' (fun m => ⟨((Ψ.ψ (Dfun m) : ↥Sh1) : Perm (Fin 16)), hDmem m⟩) (fun m m' =>
      Subtype.ext (by
        show ((Ψ.ψ (Dfun (m * m')) : ↥Sh1) : Perm (Fin 16)) =
          ((Ψ.ψ (Dfun m) : ↥Sh1) : Perm (Fin 16)) * ((Ψ.ψ (Dfun m') : ↥Sh1) : Perm (Fin 16))
        rw [hD_mul, map_mul, Subgroup.coe_mul])), fun m => by
        simp only [MonoidHom.mk'_apply, Subtype.coe_mk]⟩
  have hγinj : Function.Injective γ := by
    intro m m' hmm'
    have h0 : ((Ψ.ψ (Dfun m) : ↥Sh1) : Perm (Fin 16)) = ((Ψ.ψ (Dfun m') : ↥Sh1) : Perm (Fin 16)) := by
      rw [← hγ m, ← hγ m', hmm']
    have h2 : Dfun m = Dfun m' := Ψ.ψ.injective (Subtype.ext h0)
    have h3 : n₁.1 * (e m : G) * n₁.1⁻¹ = n₁.1 * (e m' : G) * n₁.1⁻¹ := by
      rw [← hDfun, ← hDfun, h2]
    have h4 : (e m : G) = (e m' : G) := by simpa using h3
    exact hein (Subtype.ext h4)
  have hγbij : Function.Bijective γ :=
    ⟨hγinj, Finite.injective_iff_surjective.1 hγinj⟩
  apply hNo
  refine ⟨MulEquiv.ofBijective γ hγbij, fun s i hs => ?_⟩
  rw [MulEquiv.ofBijective_apply, hγ]
  have h1 : e s = ⟨c.liftEl i, Coord5.R_le_S1 hS (c.liftEl_mem i)⟩ := by
    apply Ψ.ψ.injective
    apply Subtype.ext
    rw [he s, Subgroup.coe_inclusion, hs, Ψ.liftEl]
  have h2 : Dfun s = ⟨c.liftEl (cHat i), Coord5.R_le_S1 hS (c.liftEl_mem _)⟩ := by
    apply Subtype.ext
    rw [hDfun, h1]
    show n₁.1 * c.liftEl i * n₁.1⁻¹ = c.liftEl (cHat i)
    rw [← Coord5.rhoG_spec c n₁ i, hn₁]
  rw [h2, Ψ.liftEl]

theorem Coord5.class1_RExact
    (hS : c.S1Data S₁) (hSyl : IsSylow2In S₁ ⊤)
    (hweak : ∀ g : G, (c.lift Rm).map (MulAut.conj g).toMonoidHom ≤ S₁ →
      (c.lift Rm).map (MulAut.conj g).toMonoidHom = c.lift Rm)
    (hrho : ∀ n : ↥c.N, c.rhoG n ∈ n24L) (i j : Fin 16)
    (hij : ∃ g : G, g * c.liftEl i * g⁻¹ = c.liftEl j) : ∃ A ∈ n24L, A i = j := by
  obtain ⟨g, hg⟩ := hij
  have hab : ∀ a ∈ c.lift Rm, ∀ b ∈ c.lift Rm, a * b = b * a := fun a ha b hb =>
    Coord5.lift_comm (c := c) (M := Rm) (fun p hp q hq => Rm_comm p hp q hq) ha hb
  have hmem : (g⁻¹)⁻¹ * c.liftEl i * g⁻¹ ∈ c.lift Rm := by
    rw [inv_inv, hg]
    exact c.liftEl_mem j
  obtain ⟨n, hn, hnr⟩ := burnside_weak S₁ (c.lift Rm) hSyl.2.1 hSyl (Coord5.R_le_S1 hS) hab hweak
    (c.liftEl i) (c.liftEl_mem i) g⁻¹ hmem
  rw [inv_inv, hg] at hnr
  have hnN : n ∈ c.N := hn
  have hn'N : n⁻¹ ∈ c.N := inv_mem hnN
  refine ⟨c.rhoG ⟨n⁻¹, hn'N⟩, hrho _, ?_⟩
  apply Coord5.liftEl_inj c
  rw [Coord5.rhoG_spec]
  simpa using hnr

theorem Coord5.class1_sylow
    (hF : C1Facts2) (hRed : c.Red)
    (hAut : ∀ γ : ↥Sh1 ≃* ↥Sh1, ∀ r : ↥Sh1, (r : Perm (Fin 16)) ∈ RsubP1 →
      ((γ r : ↥Sh1) : Perm (Fin 16)) ∈ RsubP1)
    (Ψ : c.ModelIso hS Sh1 tr1 yHat1) : IsSylow2In S₁ ⊤ := by
  by_contra hns
  have hp : IsPGroup 2 ↥S₁ := IsPGroup.of_card (n := 7) (by rw [hS.card]; norm_num)
  obtain ⟨S', hS', hS₁S'⟩ := exists_sylow2_ge hp (le_top : S₁ ≤ ⊤)
  have hne : S₁ ≠ S' := fun heq => hns (heq ▸ hS')
  obtain ⟨b, hbS', hbN, hbS₁⟩ := exists_normalizer_gt hS'.2.1 hS₁S' hne
  have hbR := Coord5.class1_normalizer_R hAut Ψ hbN
  exact hbS₁ (mem_of_sylow_normalizes (Coord5.S1_sylow hF hRed hS) hS'.2.1 hS₁S' hbS' hbR)

end Class1

section Class0

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h} {S₁ : Subgroup G} {hS : c.S1Data S₁}

theorem Coord5.class0_false_of_sylow
    (hSyl : IsSylow2In S₁ ⊤) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (Ψ : c.ModelIso hS Sh0 tr16 yHat)
    (hEng : ∀ a b : ↥Sh0, (a : Perm (Fin 16)) ∈ R1subP → a * a = 1 → b * b = 1 →
      Erel Ψ.ψ a b → (b : Perm (Fin 16)) ∈ R1subP)
    (hnotge : ¬ RsubP0 ≤ R1subP) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥S₁ := hSyl.2.1
  have hidx : ¬ 2 ∣ S₁.index := by
    have h := hSyl.2.2
    rwa [Subgroup.relIndex_top_right] at h
  obtain ⟨Sy, hSy⟩ : ∃ Sy : Sylow 2 G, (Sy : Subgroup G) = S₁ :=
    ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx⟩
  let f : ↥S₁ →* Perm (Fin 16) := Sh0.subtype.comp Ψ.ψ.toMonoidHom
  set A : Subgroup G := (R1subP.comap f).map S₁.subtype with hA
  have hmemA : ∀ y, y ∈ A ↔ ∃ hy : y ∈ S₁, ((Ψ.ψ ⟨y, hy⟩ : ↥Sh0) : Perm (Fin 16)) ∈ R1subP := by
    intro y
    rw [hA, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hy, hyR⟩
      exact ⟨⟨y, hy⟩, hyR, rfl⟩
  have hAS : A ≤ (Sy : Subgroup G) := by
    rw [hSy]
    intro y hy
    exact ((hmemA y).1 hy).1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨haS, ha'⟩ := (hmemA a).1 ha
    obtain ⟨hbS, hb'⟩ := (hmemA b).1 hb
    have hc := Glue.R1L_comm_chk
    simp only [List.all_eq_true, decide_eq_true_eq] at hc
    have h1 := hc _ ha' _ hb'
    have h2 : Ψ.ψ (⟨a, haS⟩ * ⟨b, hbS⟩) = Ψ.ψ (⟨b, hbS⟩ * ⟨a, haS⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h1
    have h3 := congrArg Subtype.val (Ψ.ψ.injective h2)
    exact h3
  have hab : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have hAne : A ≠ ⊥ := by
    have hc := Glue.R1L_ne_one_chk
    simp only [List.any_eq_true, decide_eq_true_eq] at hc
    obtain ⟨r, hr, hr1⟩ := hc
    have hrSh : r ∈ Sh0 := Glue.R1subP_le_Sh0 hr
    set y : ↥S₁ := Ψ.ψ.symm ⟨r, hrSh⟩ with hy
    have hψy : Ψ.ψ y = ⟨r, hrSh⟩ := by simp [hy]
    have hyA : (y : G) ∈ A := (hmemA _).2 ⟨y.2, by
      have : (⟨(y : G), y.2⟩ : ↥S₁) = y := rfl
      rw [this, hψy]
      exact hr⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hyA
    have : y = 1 := Subtype.ext hyA
    rw [this, map_one] at hψy
    exact hr1 (congrArg Subtype.val hψy).symm
  have hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (Sy : Subgroup G) → g⁻¹ * a * g ∈ A := by
    intro a ha g hg
    rw [hSy] at hg
    obtain ⟨haS, ha'⟩ := (hmemA a).1 ha
    have hE : Erel Ψ.ψ (Ψ.ψ ⟨a, haS⟩) (Ψ.ψ ⟨g⁻¹ * a * g, hg⟩) := by
      show IsConj ((Ψ.ψ.symm (Ψ.ψ ⟨a, haS⟩) : ↥S₁) : G) ((Ψ.ψ.symm (Ψ.ψ ⟨g⁻¹ * a * g, hg⟩) : ↥S₁) : G)
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      exact isConj_iff.2 ⟨g⁻¹, by simp [mul_assoc]⟩
    have haa : Ψ.ψ ⟨a, haS⟩ * Ψ.ψ ⟨a, haS⟩ = 1 := by
      apply Subtype.ext
      have hsq := Glue.R1L_sq_chk
      simp only [List.all_eq_true, decide_eq_true_eq] at hsq
      rw [Subgroup.coe_mul]
      exact hsq _ ha'
    have haa' : a * a = 1 := by
      have h1 : (⟨a, haS⟩ : ↥S₁) * ⟨a, haS⟩ = 1 := by
        apply Ψ.ψ.injective
        rw [map_mul, haa, map_one]
      exact congrArg Subtype.val h1
    have hbb : Ψ.ψ ⟨g⁻¹ * a * g, hg⟩ * Ψ.ψ ⟨g⁻¹ * a * g, hg⟩ = 1 := by
      rw [← map_mul]
      have h1 : (⟨g⁻¹ * a * g, hg⟩ : ↥S₁) * ⟨g⁻¹ * a * g, hg⟩ = 1 := by
        apply Subtype.ext
        show g⁻¹ * a * g * (g⁻¹ * a * g) = 1
        calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
          _ = 1 := by rw [haa']; group
      rw [h1, map_one]
    exact (hmemA _).2 ⟨hg, hEng _ _ ha' haa hbb hE⟩
  have hex : ∃ i, tr16 i ∉ R1subP := by
    by_contra hcon
    apply hnotge
    intro p hp'
    rw [mem_RsubP0] at hp'
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp'
    by_contra hnot
    exact hcon ⟨j, hnot⟩
  obtain ⟨i, hi⟩ := hex
  have ht : c.liftEl i ∈ (Sy : Subgroup G) := by
    rw [hSy]
    exact Coord5.R_le_S1 hS (c.liftEl_mem i)
  have hsq : c.liftEl i ^ 2 = 1 := by
    rw [pow_two]
    exact c.liftEl_sq i
  have hmem := goldschmidt_cor hs hnab Sy A hAS hab hAne hcl _ ht hsq
  obtain ⟨hyS, hyR⟩ := (hmemA _).1 hmem
  have : (⟨c.liftEl i, hyS⟩ : ↥S₁) = ⟨c.liftEl i, Coord5.R_le_S1 hS (c.liftEl_mem i)⟩ := rfl
  rw [this, Ψ.liftEl] at hyR
  exact hi hyR

end Class0

end CFSG.GH74.GLS.C3.Layer2.L5
