module

public import CFSG.CGT.Harada80.Setting
public import CFSG.CGT.Hall82.Cocycle

public section

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)
include S

theorem blockQ_le : blockQ J ≤ J :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 J

theorem blockU_le_blockQ : blockU J ≤ blockQ J := fun _ hw => (S.short.blockU_le_center hw).1

theorem blockQ_comm_blockU {a b : G} (ha : a ∈ blockQ J) (hb : b ∈ blockU J) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (S.short.blockU_le_center hb).2 a ha

theorem blockU_comm {a b : G} (ha : a ∈ blockU J) (hb : b ∈ blockU J) : a * b = b * a := by
  have h := S.elemU.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

theorem commutator_mem_blockU {g p : G} (hg : g ∈ J) (hp : p ∈ blockQ J) :
    g * p * g⁻¹ * p⁻¹ ∈ blockU J := by
  have h : p * g * p⁻¹ * g⁻¹ ∈ blockU J := by
    change p * g * p⁻¹ * g⁻¹ ∈ ⁅blockQ J, J⁆
    simpa [commutatorElement_def] using Subgroup.commutator_mem_commutator hp hg
  have hinv := (blockU J).inv_mem h
  have e : (p * g * p⁻¹ * g⁻¹)⁻¹ = g * p * g⁻¹ * p⁻¹ := by group
  rwa [e] at hinv

theorem conj_mem_blockQ {x p : G} (hx : x ∈ M) (hp : p ∈ blockQ J) : x * p * x⁻¹ ∈ blockQ J := by
  have hxN : x ∈ Subgroup.normalizer (J : Set G) := by
    rw [S.normalizer_eq]
    exact hx
  have hxQ : x ∈ Subgroup.normalizer (blockQ J : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) J) hxN
  exact (Subgroup.mem_normalizer_iff.mp hxQ p).mp hp

theorem normalizer_blockU_eq : Subgroup.normalizer (blockU J : Set G) = M :=
  CFSG.CGT.Hall82.normalizer_blockU_eq_of_unique S.short S.normalizer_eq S.uniq

theorem conj_mem_blockU {x v : G} (hx : x ∈ M) (hv : v ∈ blockU J) : x * v * x⁻¹ ∈ blockU J := by
  have hxN : x ∈ Subgroup.normalizer (blockU J : Set G) := by
    rw [normalizer_blockU_eq S]
    exact hx
  exact (Subgroup.mem_normalizer_iff.mp hxN v).mp hv

theorem conj_mem_centralizer {x c : G} (hx : x ∈ M)
    (hc : c ∈ Subgroup.centralizer (J : Set G)) :
    x * c * x⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
  have hxN : x ∈ Subgroup.normalizer (J : Set G) := by
    rw [S.normalizer_eq]
    exact hx
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro j hj
  have hxj : x⁻¹ * j * x ∈ J := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) j).mp hj
    simpa using h
  have hc' := hc (x⁻¹ * j * x) hxj
  calc j * (x * c * x⁻¹) = x * ((x⁻¹ * j * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * j * x)) * x⁻¹ := by rw [hc']
    _ = x * c * x⁻¹ * j := by group

theorem mem_blockQ_of_forall_conj_eq {y : G} (hy : y ∈ J)
    (hc : ∀ v ∈ blockU J, y * v * y⁻¹ = v) : y ∈ blockQ J := by
  let ℓ : ↥J := ⟨y, hy⟩
  have hfix : ∀ u : ↥(blockU J),
      Multiplicative.toAdd (S.beta u) =
        ((S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
          *ᵥ Multiplicative.toAdd (S.beta u) := by
    intro u
    have hmem : y * (u : G) * y⁻¹ ∈ blockU J :=
      conj_mem_blockU S (S.le hy) u.2
    have h := S.beta_conj ℓ u ⟨y * (u : G) * y⁻¹, hmem⟩ rfl
    have heq : (⟨y * (u : G) * y⁻¹, hmem⟩ : ↥(blockU J)) = u :=
      Subtype.ext (hc (u : G) u.2)
    rwa [heq] at h
  have hmat : ((S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) = 1 := by
    ext i j
    obtain ⟨u, hu⟩ := S.beta_surjective
      (Multiplicative.ofAdd (Pi.single j (1 : ZMod 2)))
    have h := hfix u
    rw [hu] at h
    have h' : Pi.single j (1 : ZMod 2) =
        ((S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
          *ᵥ Pi.single j (1 : ZMod 2) := by
      simpa using h
    have hi := congrFun h' i
    rw [Matrix.mulVec_single_one] at hi
    rw [Matrix.one_apply]
    simpa [Pi.single_apply] using hi.symm
  have hα : S.alpha ℓ = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa using hmat
  have hker : ℓ ∈ S.alpha.ker := by
    rw [MonoidHom.mem_ker]
    exact hα
  have hmem : ℓ ∈ CFSG.pCore 2 ↥J := by
    rwa [S.ker_alpha] at hker
  exact Subgroup.mem_map.mpr ⟨ℓ, hmem, rfl⟩

private theorem cocycle_const_of_centralizer {x : G} (δ : ↥J → ↥(blockU J))
    (hδdef : ∀ g : ↥J, (δ g : G) = CFSG.CGT.Hall82.conjCocycle x (g : G))
    (hP : ∀ p ∈ blockQ J, x * p * x⁻¹ = p) :
    ∀ g h : ↥J, S.alpha g = S.alpha h → δ g = δ h := by
  have hker : ∀ g : ↥J, S.alpha g = 1 → δ g = 1 := by
    intro g hg
    have hgQ : (g : G) ∈ blockQ J := by
      have hk : g ∈ S.alpha.ker := by
        rw [MonoidHom.mem_ker]
        exact hg
      have hp : g ∈ CFSG.pCore 2 ↥J := by
        rwa [S.ker_alpha] at hk
      exact Subgroup.mem_map.mpr ⟨g, hp, rfl⟩
    apply Subtype.ext
    rw [hδdef g]
    simp only [CFSG.CGT.Hall82.conjCocycle, Subgroup.coe_one]
    rw [hP (g : G) hgQ]
    group
  intro g h hgh
  have hk : g⁻¹ * h ∈ S.alpha.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
  have hzero : δ (g⁻¹ * h) = 1 := hker (g⁻¹ * h) (MonoidHom.mem_ker.mp hk)
  have hzero' : CFSG.CGT.Hall82.conjCocycle x (((g⁻¹ * h : ↥J) : G)) = 1 := by
    rw [← hδdef (g⁻¹ * h)]
    exact congrArg Subtype.val hzero
  have hm := CFSG.CGT.Hall82.conjCocycle_mul x (g : G) (((g⁻¹ * h : ↥J) : G))
  rw [hzero', mul_one] at hm
  have harg : (g : G) * (((g⁻¹ * h : ↥J) : G)) = (h : G) := by
    simp
  rw [harg] at hm
  apply Subtype.ext
  rw [hδdef g, hδdef h]
  simpa using hm.symm

private theorem exists_cocycle_F {x : G} (δ : ↥J → ↥(blockU J))
    (hδdef : ∀ g : ↥J, (δ g : G) = CFSG.CGT.Hall82.conjCocycle x (g : G))
    (hconst : ∀ g h : ↥J, S.alpha g = S.alpha h → δ g = δ h) :
    ∃ F : ↥(omegaMinusTwo m) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2),
      (∀ g : ↥J, F (S.alpha g) = Multiplicative.toAdd (S.beta (δ g))) ∧
      ∀ ω₁ ω₂ : ↥(omegaMinusTwo m),
        F (ω₁ * ω₂) = F ω₁ +
          ((ω₁ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
            *ᵥ F ω₂ := by
  classical
  let e : ↥(omegaMinusTwo m) → ↥J := Function.surjInv S.alpha_surjective
  have he : ∀ ω, S.alpha (e ω) = ω := Function.surjInv_eq S.alpha_surjective
  let F : ↥(omegaMinusTwo m) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
    fun ω => Multiplicative.toAdd (S.beta (δ (e ω)))
  refine ⟨F, ?_, ?_⟩
  · intro g
    exact congrArg (fun u => Multiplicative.toAdd (S.beta u))
      (hconst (e (S.alpha g)) g (he (S.alpha g)))
  · intro ω₁ ω₂
    let g₁ : ↥J := e ω₁
    let g₂ : ↥J := e ω₂
    have hprod : δ (e (ω₁ * ω₂)) = δ (g₁ * g₂) := by
      apply hconst
      show S.alpha (e (ω₁ * ω₂)) = S.alpha (e ω₁ * e ω₂)
      rw [map_mul, he, he, he]
    let w : ↥(blockU J) :=
      ⟨(g₁ : G) * (δ g₂ : G) * (g₁ : G)⁻¹,
        conj_mem_blockU S (S.le g₁.2) (δ g₂).2⟩
    have hcomp : δ (g₁ * g₂) = δ g₁ * w := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hδdef (g₁ * g₂), hδdef g₁]
      change CFSG.CGT.Hall82.conjCocycle x ((g₁ : G) * (g₂ : G)) =
        CFSG.CGT.Hall82.conjCocycle x (g₁ : G) *
          ((g₁ : G) * (δ g₂ : G) * (g₁ : G)⁻¹)
      rw [hδdef g₂, CFSG.CGT.Hall82.conjCocycle_mul]
    have hw : Multiplicative.toAdd (S.beta w) =
        ((ω₁ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
          *ᵥ Multiplicative.toAdd (S.beta (δ g₂)) := by
      have h := S.beta_conj g₁ (δ g₂) w rfl
      rwa [he ω₁] at h
    calc F (ω₁ * ω₂) = Multiplicative.toAdd (S.beta (δ (e (ω₁ * ω₂)))) := rfl
      _ = Multiplicative.toAdd (S.beta (δ (g₁ * g₂))) := by rw [hprod]
      _ = Multiplicative.toAdd (S.beta (δ g₁ * w)) := by rw [hcomp]
      _ = Multiplicative.toAdd (S.beta (δ g₁) * S.beta w) := by rw [map_mul]
      _ = Multiplicative.toAdd (S.beta (δ g₁)) +
          Multiplicative.toAdd (S.beta w) := by rw [toAdd_mul]
      _ = F ω₁ +
          ((ω₁ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
            *ᵥ F ω₂ := by rw [hw]

private theorem coboundary_eq_of_cocycle_F (hZ : blockZ J = ⊥)
    (δ : ↥J → ↥(blockU J))
    (F : ↥(omegaMinusTwo m) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2))
    (hFα : ∀ g : ↥J, F (S.alpha g) = Multiplicative.toAdd (S.beta (δ g)))
    {a : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2}
    (ha : ∀ ω : ↥(omegaMinusTwo m),
      F ω = ((ω : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a - a)
    (v : ↥(blockU J)) (hv : Multiplicative.toAdd (S.beta v) = a)
    (w : ↥J → ↥(blockU J))
    (hwdef : ∀ g : ↥J, (w g : G) = (g : G) * (v : G) * (g : G)⁻¹) :
    ∀ g : ↥J, δ g = w g * v⁻¹ := by
  have hβinj : Function.Injective S.beta := by
    rw [← MonoidHom.ker_eq_bot_iff, S.ker_beta, hZ]
    simp
  intro g
  apply hβinj
  have hwg : Multiplicative.toAdd (S.beta (w g)) =
      ((S.alpha g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
        *ᵥ Multiplicative.toAdd (S.beta v) :=
    S.beta_conj g v (w g) (hwdef g)
  have hha := ha (S.alpha g)
  rw [hFα g, ← hv] at hha
  have hR : Multiplicative.toAdd (S.beta (w g * v⁻¹)) =
      ((S.alpha g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))
        *ᵥ Multiplicative.toAdd (S.beta v) - Multiplicative.toAdd (S.beta v) := by
    rw [map_mul, toAdd_mul, hwg]
    have hinv : Multiplicative.toAdd (S.beta v⁻¹) = - Multiplicative.toAdd (S.beta v) := by
      rw [map_inv, toAdd_inv]
    rw [hinv]
    abel
  have hto : Multiplicative.toAdd (S.beta (δ g)) =
      Multiplicative.toAdd (S.beta (w g * v⁻¹)) := hha.trans hR.symm
  simpa using congrArg Multiplicative.ofAdd hto

private theorem conj_mul_mem_centralizer_of_cocycle {x v : G} (hv : v ∈ blockU J)
    (hδ : ∀ g ∈ J, CFSG.CGT.Hall82.conjCocycle x g = (g * v * g⁻¹) * v⁻¹) :
    v * x ∈ Subgroup.centralizer (J : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hxl : x * g * x⁻¹ = CFSG.CGT.Hall82.conjCocycle x g * g := by
    simp only [CFSG.CGT.Hall82.conjCocycle]
    group
  have hconj : (v * x) * g * (v * x)⁻¹ = g := by
    calc (v * x) * g * (v * x)⁻¹
        = v * (x * g * x⁻¹) * v⁻¹ := by group
      _ = v * (CFSG.CGT.Hall82.conjCocycle x g * g) * v⁻¹ := by rw [hxl]
      _ = v * (((g * v * g⁻¹) * v⁻¹) * g) * v⁻¹ := by rw [hδ g hg]
      _ = g := by
        have hcomm : v * (g * v * g⁻¹) = (g * v * g⁻¹) * v :=
          blockU_comm S hv (conj_mem_blockU S (S.le hg) hv)
        calc v * (((g * v * g⁻¹) * v⁻¹) * g) * v⁻¹
            = (v * (g * v * g⁻¹)) * v⁻¹ * g * v⁻¹ := by group
          _ = ((g * v * g⁻¹) * v) * v⁻¹ * g * v⁻¹ := by rw [hcomm]
          _ = g := by group
  calc g * (v * x) = ((v * x) * g * (v * x)⁻¹) * (v * x) := by rw [hconj]
    _ = (v * x) * g := by group

theorem exists_mul_mem_centralizer (hH1 : H1Natural m) (hZ : blockZ J = ⊥) {x : G}
    (hδ : ∀ g ∈ J, x * g * x⁻¹ * g⁻¹ ∈ blockU J) (hP : ∀ p ∈ blockQ J, x * p * x⁻¹ = p) :
    ∃ v ∈ blockU J, v * x ∈ Subgroup.centralizer (J : Set G) := by
  classical
  let δ : ↥J → ↥(blockU J) := fun g =>
    ⟨CFSG.CGT.Hall82.conjCocycle x (g : G), hδ (g : G) g.2⟩
  have hδdef : ∀ g : ↥J, (δ g : G) = CFSG.CGT.Hall82.conjCocycle x (g : G) :=
    fun _ => rfl
  have hconst := cocycle_const_of_centralizer S δ hδdef hP
  obtain ⟨F, hFα, hFcoc⟩ := exists_cocycle_F S δ hδdef hconst
  obtain ⟨a, ha⟩ := hH1 F hFcoc
  obtain ⟨v, hv⟩ := S.beta_surjective (Multiplicative.ofAdd a)
  have hv' : Multiplicative.toAdd (S.beta v) = a := by
    rw [hv]
    rfl
  let w : ↥J → ↥(blockU J) := fun g =>
    ⟨(g : G) * (v : G) * (g : G)⁻¹, conj_mem_blockU S (S.le g.2) v.2⟩
  have hwdef : ∀ g : ↥J, (w g : G) = (g : G) * (v : G) * (g : G)⁻¹ := fun _ => rfl
  have hδeq := coboundary_eq_of_cocycle_F S hZ δ F hFα ha v hv' w hwdef
  refine ⟨v, v.2, conj_mul_mem_centralizer_of_cocycle (x := x) S v.2 ?_⟩
  intro g hg
  have h := congrArg Subtype.val (hδeq ⟨g, hg⟩)
  simpa [w, hwdef, hδdef, CFSG.CGT.Hall82.conjCocycle, mul_assoc] using h

theorem blockQ_comm (hZ : blockZ J = ⊥) {a b : G} (ha : a ∈ blockQ J) (hb : b ∈ blockQ J) :
    a * b = b * a := by
  let c : G := a * b * a⁻¹ * b⁻¹
  have hAB : ⁅a, b⁆ ∈ blockU J := by
    change ⁅a, b⁆ ∈ ⁅blockQ J, J⁆
    exact Subgroup.commutator_mem_commutator ha (blockQ_le S hb)
  have hcA : c ∈ blockU J := by
    simpa [c, commutatorElement_def] using hAB
  have hcC : c ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    let u : G := g * a * g⁻¹ * a⁻¹
    let v : G := g * b * g⁻¹ * b⁻¹
    have hu : u ∈ blockU J := commutator_mem_blockU S hg ha
    have hv : v ∈ blockU J := commutator_mem_blockU S hg hb
    have hua : u * a = a * u := (blockQ_comm_blockU S ha hu).symm
    have hub : u * b = b * u := (blockQ_comm_blockU S hb hu).symm
    have hva : a * v = v * a := blockQ_comm_blockU S ha hv
    have hvb : v * b = b * v := (blockQ_comm_blockU S hb hv).symm
    have huv : u * v = v * u := blockU_comm S hu hv
    have hga : g * a * g⁻¹ = u * a := by
      simp only [u]
      group
    have hgb : g * b * g⁻¹ = v * b := by
      simp only [v]
      group
    have hcommut : ⁅u * a, v * b⁆ = ⁅a, b⁆ := by
      have h1 : ⁅u, v * b⁆ = 1 := by
        rw [commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_mul_comm.mpr huv,
          commutatorElement_eq_one_iff_mul_comm.mpr hub]
        group
      have h2 : ⁅a, v * b⁆ = ⁅a, b⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_mul_comm.mpr hva, one_mul]
        rw [blockU_comm S hv hAB]
        group
      rw [commutatorElement_mul_left_eq_conj_mul, h1, mul_one, h2]
      rw [blockU_comm S hu hAB]
      group
    have hconj : g * c * g⁻¹ = c := by
      rw [show c = ⁅a, b⁆ from rfl]
      calc g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ :=
            conjugate_commutatorElement (g₁ := a) (g₂ := b) (g₃ := g)
        _ = ⁅u * a, v * b⁆ := by rw [hga, hgb]
        _ = ⁅a, b⁆ := hcommut
        _ = c := rfl
    calc g * c = (g * c * g⁻¹) * g := by group
      _ = c * g := by rw [hconj]
  have hcZ : c ∈ blockZ J := Subgroup.mem_inf.mpr ⟨hcA, hcC⟩
  rw [hZ] at hcZ
  have hc1 : c = 1 := Subgroup.mem_bot.mp hcZ
  exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [c, commutatorElement_def] using hc1)

theorem exists_mul_of_mem_blockQ (hH1 : H1Natural m) (hZ : blockZ J = ⊥) {p : G}
    (hp : p ∈ blockQ J) :
    ∃ c ∈ blockQ J ⊓ Subgroup.centralizer (J : Set G), ∃ v ∈ blockU J, p = c * v := by
  have hδp : ∀ g ∈ J, p * g * p⁻¹ * g⁻¹ ∈ blockU J := by
    intro g hg
    have h : ⁅p, g⁆ ∈ blockU J := by
      change ⁅p, g⁆ ∈ ⁅blockQ J, J⁆
      exact Subgroup.commutator_mem_commutator hp hg
    simpa [commutatorElement_def] using h
  obtain ⟨v, hv, hvc⟩ := exists_mul_mem_centralizer (x := p) S hH1 hZ hδp
    (fun q hq => by
      have h := blockQ_comm S hZ hp hq
      rw [h]
      group)
  refine ⟨v * p, ?_, v⁻¹, (blockU J).inv_mem hv, ?_⟩
  · exact Subgroup.mem_inf.mpr ⟨(blockQ J).mul_mem (blockU_le_blockQ S hv) hp, hvc⟩
  · have hcomm : v * p * v⁻¹ = p := by
      rw [← blockQ_comm_blockU S hp hv]
      group
    calc p = v * p * v⁻¹ := hcomm.symm
      _ = (v * p) * v⁻¹ := by group

theorem blockQ_inf_centralizer_inf_blockU (hZ : blockZ J = ⊥) :
    blockQ J ⊓ Subgroup.centralizer (J : Set G) ⊓ blockU J = ⊥ := by
  rw [eq_bot_iff]
  calc blockQ J ⊓ Subgroup.centralizer (J : Set G) ⊓ blockU J
      = blockU J ⊓ (blockQ J ⊓ Subgroup.centralizer (J : Set G)) := by rw [inf_comm]
    _ ≤ blockU J ⊓ Subgroup.centralizer (J : Set G) := inf_le_inf_left _ inf_le_right
    _ = blockZ J := rfl
    _ = ⊥ := hZ

private theorem conjCocycle_mem_blockQ_of_centralizer {x g : G} (hx : x ∈ M) (hg : g ∈ J)
    (hxA : ∀ v ∈ blockU J, x * v * x⁻¹ = v) :
    CFSG.CGT.Hall82.conjCocycle x g ∈ blockQ J := by
  have hy : CFSG.CGT.Hall82.conjCocycle x g ∈ J :=
    J.mul_mem (S.normal hx hg) (J.inv_mem hg)
  apply mem_blockQ_of_forall_conj_eq S hy
  intro v hv
  have hgv : g⁻¹ * v * g ∈ blockU J := by
    simpa using conj_mem_blockU S (S.le (J.inv_mem hg)) hv
  have hxgy : x⁻¹ * (g⁻¹ * v * g) * x = g⁻¹ * v * g := by
    have h := hxA (g⁻¹ * v * g) hgv
    calc x⁻¹ * (g⁻¹ * v * g) * x = x⁻¹ * (x * (g⁻¹ * v * g) * x⁻¹) * x := by rw [h]
      _ = g⁻¹ * v * g := by group
  simp only [CFSG.CGT.Hall82.conjCocycle]
  calc x * g * x⁻¹ * g⁻¹ * v * (x * g * x⁻¹ * g⁻¹)⁻¹
      = x * (g * (x⁻¹ * (g⁻¹ * v * g) * x) * g⁻¹) * x⁻¹ := by group
    _ = x * (g * (g⁻¹ * v * g) * g⁻¹) * x⁻¹ := by rw [hxgy]
    _ = x * v * x⁻¹ := by group
    _ = v := hxA v hv

private theorem conjCocycle_mem_blockU_of_centralizer (hH1 : H1Natural m)
    (hZ : blockZ J = ⊥) {x : G} (hx : x ∈ M)
    (hxA : ∀ v ∈ blockU J, x * v * x⁻¹ = v) {g : G}
    (hg : g ∈ J) : CFSG.CGT.Hall82.conjCocycle x g ∈ blockU J := by
  let D : Subgroup G := blockQ J ⊓ Subgroup.centralizer (J : Set G)
  have hLV : J ≤ Subgroup.normalizer (blockU J : Set G) := by
    rw [normalizer_blockU_eq S]
    exact S.le
  have hδ' : ∀ l ∈ J, ∃ d ∈ D, ∃ v ∈ blockU J,
      CFSG.CGT.Hall82.conjCocycle x l = d * v := by
    intro l hl
    exact exists_mul_of_mem_blockQ S hH1 hZ
      (conjCocycle_mem_blockQ_of_centralizer S hx hl hxA)
  exact CFSG.CGT.Hall82.conjCocycle_mul_mem_of_perfect (L := J) (V := blockU J)
    (D := D) (x := x) hLV inf_le_right
    (fun a ha b hb => blockQ_comm S hZ ha.1 hb.1)
    (by simpa [D] using blockQ_inf_centralizer_inf_blockU S hZ)
    (fun d hd v hv => blockQ_comm_blockU S hd.1 hv) S.perfect hδ' g hg

theorem conj_eq_of_centralizer (hH1 : H1Natural m) (hZ : blockZ J = ⊥) {x : G} (hx : x ∈ M)
    (hxA : ∀ v ∈ blockU J, x * v * x⁻¹ = v) {p : G} (hp : p ∈ blockQ J) :
    x * p * x⁻¹ = p := by
  let D : Subgroup G := blockQ J ⊓ Subgroup.centralizer (J : Set G)
  obtain ⟨c, hc, v, hv, hp_eq⟩ := exists_mul_of_mem_blockQ S hH1 hZ hp
  have hδA : CFSG.CGT.Hall82.conjCocycle x p ∈ blockU J :=
    conjCocycle_mem_blockU_of_centralizer S hH1 hZ hx hxA (blockQ_le S hp)
  have hδD : CFSG.CGT.Hall82.conjCocycle x p ∈ D := by
    have hcQ : x * c * x⁻¹ ∈ blockQ J := conj_mem_blockQ S hx hc.1
    have hcC : x * c * x⁻¹ ∈ Subgroup.centralizer (J : Set G) :=
      conj_mem_centralizer S hx hc.2
    have hconj : CFSG.CGT.Hall82.conjCocycle x p = (x * c * x⁻¹) * c⁻¹ := by
      simp only [CFSG.CGT.Hall82.conjCocycle]
      rw [hp_eq]
      calc x * (c * v) * x⁻¹ * (c * v)⁻¹
          = (x * c * x⁻¹) * (x * v * x⁻¹) * v⁻¹ * c⁻¹ := by group
        _ = (x * c * x⁻¹) * v * v⁻¹ * c⁻¹ := by rw [hxA v hv]
        _ = (x * c * x⁻¹) * c⁻¹ := by group
    rw [hconj]
    exact Subgroup.mem_inf.mpr ⟨(blockQ J).mul_mem hcQ ((blockQ J).inv_mem hc.1),
      (Subgroup.centralizer (J : Set G)).mul_mem hcC
        ((Subgroup.centralizer (J : Set G)).inv_mem hc.2)⟩
  have hδbot : CFSG.CGT.Hall82.conjCocycle x p ∈ D ⊓ blockU J :=
    Subgroup.mem_inf.mpr ⟨hδD, hδA⟩
  have hδ1 : CFSG.CGT.Hall82.conjCocycle x p = 1 := by
    have h := hδbot
    rw [show D ⊓ blockU J = ⊥ from blockQ_inf_centralizer_inf_blockU S hZ] at h
    exact Subgroup.mem_bot.mp h
  calc x * p * x⁻¹ = CFSG.CGT.Hall82.conjCocycle x p * p := by
        simp only [CFSG.CGT.Hall82.conjCocycle]
        group
    _ = p := by rw [hδ1, one_mul]

theorem exists_mul_mem_centralizer_of_centralizer (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    {x : G} (hx : x ∈ M) (hxA : ∀ v ∈ blockU J, x * v * x⁻¹ = v) :
    ∃ v ∈ blockU J, v * x ∈ Subgroup.centralizer (J : Set G) :=
  exists_mul_mem_centralizer S hH1 hZ
    (fun g hg => conjCocycle_mem_blockU_of_centralizer S hH1 hZ hx hxA hg)
    (fun p hp => conj_eq_of_centralizer S hH1 hZ hx hxA hp)

private theorem le_normalizer_blockU_inf_centralizer {x : G}
    (hxJ : ∀ g ∈ J, x * g * x⁻¹ * g⁻¹ ∈ blockQ J) :
    J ≤ Subgroup.normalizer
      ((blockU J ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg w hw
  have hwA : (w : G) ∈ blockU J := (Subgroup.mem_inf.mp hw).1
  have hwC : w ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hw).2
  have hgwA : g * (w : G) * g⁻¹ ∈ blockU J := conj_mem_blockU S (S.le hg) hwA
  refine Subgroup.mem_inf.mpr ⟨hgwA, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  let q : G := x * g * x⁻¹ * g⁻¹
  have hq : q ∈ blockQ J := hxJ g hg
  have hxw : x * (w : G) * x⁻¹ = (w : G) := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hwC
    calc x * (w : G) * x⁻¹ = ((w : G) * x) * x⁻¹ := by rw [← hcomm]
      _ = (w : G) := by group
  have hxg : x * g * x⁻¹ = q * g := by
    simp only [q]
    group
  have hconj : x * (g * (w : G) * g⁻¹) * x⁻¹ = g * (w : G) * g⁻¹ := by
    calc x * (g * (w : G) * g⁻¹) * x⁻¹
        = (x * g * x⁻¹) * (x * (w : G) * x⁻¹) * (x * g * x⁻¹)⁻¹ := by group
      _ = (q * g) * (w : G) * (q * g)⁻¹ := by rw [hxw, hxg]
      _ = q * (g * (w : G) * g⁻¹) * q⁻¹ := by group
      _ = g * (w : G) * g⁻¹ := by
        rw [blockQ_comm_blockU S hq hgwA]
        group
  have hxw' : x * (g * (w : G) * g⁻¹) = (g * (w : G) * g⁻¹) * x := by
    calc x * (g * (w : G) * g⁻¹)
        = (x * (g * (w : G) * g⁻¹) * x⁻¹) * x := by group
      _ = (g * (w : G) * g⁻¹) * x := by rw [hconj]
  exact hxw'.symm

private theorem exists_ne_one_mem_blockU_centralizer_zpowers (hZ : blockZ J = ⊥)
    {x : G} (hx : x ∈ M) (h2 : ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    ∃ w ∈ blockU J, w ≠ 1 ∧ w * x = x * w := by
  have hAne : blockU J ≠ ⊥ := by
    have hlt := S.short.blockZ_lt_blockU
    rw [hZ] at hlt
    exact bot_lt_iff_ne_bot.mp hlt
  have hA2 : IsPGroup 2 (blockU J) :=
    CFSG.CGT.PushingUpLit.SolK.isPGroup_of_le
      (CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' J) (blockU_le_blockQ S)
  have hX2 : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := h2
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  have hxN : x ∈ Subgroup.normalizer (blockU J : Set G) := by
    rw [normalizer_blockU_eq S]
    exact hx
  have hXA : Subgroup.zpowers x ≤ Subgroup.normalizer (blockU J : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  set P : Subgroup G := blockU J ⊔ Subgroup.zpowers x with hP
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hA2 hX2 hXA
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hAP : blockU J ≤ P := le_sup_left
  have hXP : Subgroup.zpowers x ≤ P := le_sup_right
  have hN : ((blockU J).subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAP]
    intro a g ha hg
    have hle : P ≤ Subgroup.normalizer (blockU J : Set G) :=
      sup_le Subgroup.le_normalizer hXA
    exact (Subgroup.mem_normalizer_iff.1 (hle hg) a).1 ha
  have hne' : (blockU J).subgroupOf P ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [eq_bot_iff]
    intro a ha
    have hmem : (⟨a, hAP ha⟩ : ↥P) ∈ (blockU J).subgroupOf P :=
      Subgroup.mem_subgroupOf.2 ha
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  obtain ⟨hwA, hwc⟩ := Subgroup.mem_inf.1 hw
  refine ⟨(w : G), Subgroup.mem_subgroupOf.1 hwA, ?_, ?_⟩
  · intro h1
    exact hw1 (Subtype.ext (Subtype.ext h1))
  · have hcenter := Subgroup.mem_center_iff.1 hwc ⟨x, hXP (Subgroup.mem_zpowers x)⟩
    exact (congrArg Subtype.val hcenter).symm

theorem conj_eq_of_isPGroup (hZ : blockZ J = ⊥) {x : G} (hx : x ∈ M)
    (h2 : ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hxJ : ∀ g ∈ J, x * g * x⁻¹ * g⁻¹ ∈ blockQ J) {v : G} (hv : v ∈ blockU J) :
    x * v * x⁻¹ = v := by
  obtain ⟨w, hwA, hw1, hwx⟩ :=
    exists_ne_one_mem_blockU_centralizer_zpowers S hZ hx h2
  have hJK := le_normalizer_blockU_inf_centralizer S hxJ
  have hZK : blockZ J ≤ blockU J ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [hZ]
    exact bot_le
  have hwK : w ∈ blockU J ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hwA, Subgroup.mem_centralizer_singleton_iff.mpr hwx⟩
  rcases S.short.irreducible (blockU J ⊓ Subgroup.centralizer ({x} : Set G))
    hZK inf_le_left hJK with hKZ | hKU
  · rw [hKZ, hZ] at hwK
    exact absurd (Subgroup.mem_bot.mp hwK) hw1
  · have hvK : v ∈ blockU J ⊓ Subgroup.centralizer ({x} : Set G) := by
      rw [hKU]
      exact hv
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hvK).2
    calc x * v * x⁻¹ = (x * v) * x⁻¹ := by group
      _ = (v * x) * x⁻¹ := by rw [← hcomm]
      _ = v := by group

theorem mem_blockU_of_centralizer (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {x : G} (hx : x ∈ M)
    (hxA : ∀ v ∈ blockU J, x * v * x⁻¹ = v) : x ∈ blockU J := by
  obtain ⟨v, hv, hvx⟩ := exists_mul_mem_centralizer_of_centralizer S hH1 hZ hx hxA
  have hvx1 : v * x = 1 := by
    have h : v * x ∈ (⊥ : Subgroup G) := by
      simpa [hC] using hvx
    exact Subgroup.mem_bot.mp h
  have hx_eq : x = v⁻¹ := by
    calc x = v⁻¹ * (v * x) := by group
      _ = v⁻¹ * 1 := by rw [hvx1]
      _ = v⁻¹ := mul_one _
  rw [hx_eq]
  exact (blockU J).inv_mem hv

end CFSG.CGT.Harada80.Setting
