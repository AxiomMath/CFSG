module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.HardMathSupport.MathTwE6

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] noncomputable def normalizerToMulAut (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) →* MulAut J where
  toFun g :=
    { toFun := fun x => ⟨(g : G) * x * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.1 g.2 x).1 x.2⟩
      invFun := fun x => ⟨(g : G)⁻¹ * x * g, (Subgroup.mem_normalizer_iff''.1 g.2 x).1 x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_assoc]

theorem normalizerToMulAut_apply (J : Subgroup G) (g : Subgroup.normalizer (J : Set G)) (x : J) :
    ((normalizerToMulAut J g x : J) : G) = (g : G) * x * (g : G)⁻¹ := rfl

theorem mem_ker_normalizerToMulAut (J : Subgroup G) (g : Subgroup.normalizer (J : Set G)) :
    g ∈ (normalizerToMulAut J).ker ↔ (g : G) ∈ Subgroup.centralizer (J : Set G) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have := congrArg (fun φ : MulAut J => ((φ ⟨x, hx⟩ : J) : G)) h
    simp only [normalizerToMulAut_apply, MulAut.one_apply] at this
    calc x * (g : G) = ((g : G) * x * (g : G)⁻¹) * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [normalizerToMulAut_apply, MulAut.one_apply]
    rw [← h x x.2]
    group

theorem mem_normalizer_centralizer {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (J : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have hy' : g⁻¹ * y * g ∈ J := (Subgroup.mem_normalizer_iff''.1 hg y).1 hy
    have h := hx _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group
  · intro hx y hy
    have hy' : g * y * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hg y).1 hy
    have h := hx _ hy'
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = x * y := by group

theorem map_conj_eq_iff_mem_normalizer [Finite G] (J : Subgroup G) (g : G) :
    J.map (MulAut.conj g).toMonoidHom = J ↔ g ∈ Subgroup.normalizer (J : Set G) := by
  constructor
  · intro h
    have hle : ∀ x ∈ J, g * x * g⁻¹ ∈ J := fun x hx => by
      rw [← h]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hle x, fun hx => ?_⟩
    have hx' : g * x * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := by rw [h]; exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      simpa using hyx
    exact this ▸ hy
  · intro hg
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff''.1 hg x).1 hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_map_conj (J : Subgroup G) (a b : G) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (J : Subgroup G) : J.map (MulAut.conj (1 : G)).toMonoidHom = J := by
  ext x
  simp [MulAut.conj_apply]

variable [Finite G]

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set Nr := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ Nr := Subgroup.le_normalizer
  have : (A.subgroupOf Nr).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ Y : Subgroup G, Y ≤ Nr → Nat.card (Y.subgroupOf Nr) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf Nr) (K := B.subgroupOf Nr ⊔ A.subgroupOf Nr)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf Nr) (K := B.subgroupOf Nr)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : A.subgroupOf Nr ≤ _)] at h1
  rw [inf_comm] at h2
  have hsup : B.subgroupOf Nr ⊔ A.subgroupOf Nr = (A ⊔ B).subgroupOf Nr := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf Nr ⊓ A.subgroupOf Nr = (A ⊓ B).subgroupOf Nr := by
    ext
    simp [Subgroup.mem_subgroupOf, and_comm]
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ hB, hc _ (inf_le_left.trans hAN)] at h2
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A.subgroupOf Nr).relIndex (B.subgroupOf Nr) * Nat.card A) *
          Nat.card ↥(A ⊓ B) := by rw [h1]
    _ = Nat.card A * ((A.subgroupOf Nr).relIndex (B.subgroupOf Nr) * Nat.card ↥(A ⊓ B)) := by
          ring
    _ = Nat.card A * Nat.card B := by rw [h2]

theorem card_le_pow_factorization {p : ℕ} (hp : p.Prime) {P H : Subgroup G} (hPH : P ≤ H)
    (hP : IsPGroup p P) : Nat.card P ≤ p ^ (Nat.card H).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : p ^ k ∣ Nat.card H := hk ▸ Subgroup.card_dvd_of_le hPH
  have hle : k ≤ (Nat.card H).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hle

theorem card_le_three_of_le_centralizer (w : G) (hw : w ^ 3 = 1) (Q L : Subgroup G)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hL3 : (Nat.card G).factorization 3 ≤ (Nat.card L).factorization 3)
    (hCL : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) ⊓ L → IsPGroup 3 P →
      P ≤ Subgroup.zpowers w) :
    ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup 3 P → Nat.card P ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (Q : Set G) with hCdef
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := fun l hl => mem_normalizer_centralizer (hLQ hl)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hLC
  have hne : ∀ H : Subgroup G, Nat.card H ≠ 0 := fun H => Nat.card_pos.ne'
  have hf := congrArg (fun m => m.factorization 3) hprod
  simp only [Nat.factorization_mul (hne _) (hne _), Finsupp.add_apply] at hf
  have hsupG : (Nat.card ↥(C ⊔ L)).factorization 3 ≤ (Nat.card G).factorization 3 :=
    (Nat.factorization_le_iff_dvd (hne _) Nat.card_pos.ne').2 (Subgroup.card_subgroup_dvd_card _) 3
  have hinf : (Nat.card ↥(C ⊓ L)).factorization 3 ≤ 1 := by
    obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 ↥(C ⊓ L)))
    set R' : Subgroup G := (R : Subgroup ↥(C ⊓ L)).map (C ⊓ L).subtype
    have hR'le : R' ≤ C ⊓ L := Subgroup.map_subtype_le _
    have hR'w := hCL R' hR'le (R.isPGroup'.map _)
    have hcR : Nat.card R' = 3 ^ (Nat.card ↥(C ⊓ L)).factorization 3 := by
      rw [Subgroup.card_map_of_injective (C ⊓ L).subtype_injective, Sylow.card_eq_multiplicity]
    have hw3 : Nat.card (Subgroup.zpowers w) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hw)
    have h3 : 3 ^ (Nat.card ↥(C ⊓ L)).factorization 3 ≤ 3 ^ 1 := by
      rw [← hcR, pow_one]
      exact (Subgroup.card_le_of_le hR'w).trans hw3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have hC : (Nat.card C).factorization 3 ≤ 1 := by omega
  intro P hPC hP
  calc Nat.card P ≤ 3 ^ (Nat.card C).factorization 3 := card_le_pow_factorization Nat.prime_three hPC hP
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hC
    _ = 3 := pow_one 3

theorem pow_card_dvd_of_commute (S : Finset (Subgroup G)) (d : ℕ)
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hd : ∀ J ∈ S, d ∣ (Subgroup.center J).index) : d ^ S.card ∣ Nat.card G := by
  classical
  suffices h : ∀ T ⊆ S, d ^ T.card ∣ Nat.card ↥(⨆ J ∈ T, J) from
    (h S le_rfl).trans (Subgroup.card_subgroup_dvd_card _)
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | insert J T hJT ih =>
    intro hTS
    have hJS : J ∈ S := hTS (Finset.mem_insert_self J T)
    have hT : T ⊆ S := (Finset.subset_insert J T).trans hTS
    set M : Subgroup G := ⨆ B ∈ T, B with hMdef
    have hMC : M ≤ Subgroup.centralizer (J : Set G) := by
      refine iSup₂_le fun B hB => ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hne : J ≠ B := fun h => hJT (h ▸ hB)
      exact hcomm J hJS B (hT hB) hne a ha b hb
    have hJM : J ≤ Subgroup.normalizer (M : Set G) := by
      have : J ≤ Subgroup.centralizer (M : Set G) := Subgroup.le_centralizer_iff.1 hMC
      exact this.trans (Subgroup.centralizer_le_normalizer _)
    have hprod := card_sup_mul_card_inf_of_le_normalizer hJM
    have hrel := Subgroup.relIndex_mul_card (H := M) (K := J)
    have hcen : M.subgroupOf J ≤ Subgroup.center J := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hxC := hMC (Subgroup.mem_subgroupOf.1 hx)
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxC) y y.2)
    have hdrel : d ∣ M.relIndex J := (hd J hJS).trans (Subgroup.index_dvd_of_le hcen)
    have hsup : (⨆ B ∈ insert J T, B) = M ⊔ J := by
      rw [Finset.iSup_insert, sup_comm]
    have hcard : Nat.card ↥(M ⊔ J) = Nat.card M * M.relIndex J := by
      have hpos : Nat.card ↥(M ⊓ J) ≠ 0 := Nat.card_pos.ne'
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos)
      rw [hprod, ← hrel]
      ring
    rw [hsup, hcard, Finset.card_insert_of_notMem hJT, pow_succ]
    exact Nat.mul_dvd_mul (ih hT) hdrel

theorem relIndex_dvd_card_mulAut (w : G) (Q L : Subgroup G) (S : Finset (Subgroup G)) (n : ℕ)
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hS : ∀ g ∈ L, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S)
    (hSn : S.card ≤ n) (h9 : ∀ J ∈ S, 9 ∣ Nat.card J)
    (hCQ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup 3 P →
      Nat.card P ≤ 3)
    (hdich : ∀ N : Subgroup G, N ≤ Q →
      (∀ g ∈ L, g ^ n.factorial ∈ Subgroup.normalizer (N : Set G)) →
        N ≤ Subgroup.zpowers w ∨ N = Q)
    (hidx : ¬ (Subgroup.zpowers w).relIndex Q ∣ n.factorial) :
    ∀ J ∈ S, (Subgroup.zpowers w).relIndex Q ∣ Nat.card (MulAut J) := by
  classical
  let act : L → S → S := fun g J => ⟨J.1.map (MulAut.conj (g : G)).toMonoidHom, hS g g.2 J J.2⟩
  have hact_mul : ∀ a b : L, ∀ J : S, act (a * b) J = act a (act b J) := fun a b J =>
    Subtype.ext (by simp only [act, Subgroup.coe_mul]; exact (map_conj_map_conj J.1 b a).symm)
  have hact_one : ∀ J : S, act 1 J = J := fun J =>
    Subtype.ext (by simp only [act, OneMemClass.coe_one]; exact map_conj_one J.1)
  let φ : L →* Equiv.Perm S :=
    { toFun := fun g =>
        { toFun := act g
          invFun := act g⁻¹
          left_inv := fun J => by rw [← hact_mul, inv_mul_cancel, hact_one]
          right_inv := fun J => by rw [← hact_mul, mul_inv_cancel, hact_one] }
      map_one' := Equiv.ext hact_one
      map_mul' := fun a b => Equiv.ext (hact_mul a b) }
  have hφ : ∀ (g : L) (J : S), ((φ g J : S) : Subgroup G) = J.1.map (MulAut.conj (g : G)).toMonoidHom :=
    fun _ _ => rfl
  have hcardS : Nat.card (Equiv.Perm S) ∣ n.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Nat.factorial_dvd_factorial hSn
  have hpow : ∀ g ∈ L, ∀ J ∈ S, J.map (MulAut.conj (g ^ n.factorial)).toMonoidHom = J := by
    intro g hg J hJ
    have h1 : φ ⟨g, hg⟩ ^ n.factorial = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard _).trans hcardS)
    have h2 := congrArg (fun σ : Equiv.Perm S => ((σ ⟨J, hJ⟩ : S) : Subgroup G)) h1
    simp only [← map_pow, hφ, Equiv.Perm.coe_one, id_eq, SubgroupClass.coe_pow] at h2
    exact h2
  have hpowN : ∀ g ∈ L, g ^ n.factorial ∈ L := fun g hg => L.pow_mem hg _
  have hpowJ : ∀ g ∈ L, ∀ J ∈ S, g ^ n.factorial ∈ Subgroup.normalizer (J : Set G) :=
    fun g hg J hJ => (map_conj_eq_iff_mem_normalizer J _).1 (hpow g hg J hJ)
  let ψ : Q →* Equiv.Perm S := φ.comp (Subgroup.inclusion hQL)
  set N : Subgroup G := ψ.ker.map Q.subtype with hNdef
  have hmemN : ∀ x : G, x ∈ N ↔ x ∈ Q ∧ ∀ J ∈ S, x ∈ Subgroup.normalizer (J : Set G) := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun J hJ => (map_conj_eq_iff_mem_normalizer J _).1 ?_⟩
      have h2 := congrArg (fun σ : Equiv.Perm S => ((σ ⟨J, hJ⟩ : S) : Subgroup G))
        (MonoidHom.mem_ker.1 hy)
      exact h2
    · rintro ⟨hxQ, hxJ⟩
      refine ⟨⟨x, hxQ⟩, MonoidHom.mem_ker.2 (Equiv.ext fun J => Subtype.ext ?_), rfl⟩
      exact (map_conj_eq_iff_mem_normalizer J.1 x).2 (hxJ J.1 J.2)
  have hNQ : N ≤ Q := Subgroup.map_subtype_le _
  have hNnorm : ∀ g ∈ L, g ^ n.factorial ∈ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hyQ := hLQ (hpowN g hg)
    rw [hmemN, hmemN, Subgroup.mem_normalizer_iff.1 hyQ x]
    refine and_congr_right fun _ => forall₂_congr fun J hJ => ?_
    have hyJ := hpowJ g hg J hJ
    constructor
    · intro hx
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyJ hx) (Subgroup.inv_mem _ hyJ)
    · intro hx
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyJ) hx) hyJ
      simpa [mul_assoc] using this
  have hQS : ∀ q ∈ Q, ∀ J ∈ S, q ∈ Subgroup.normalizer (J : Set G) := by
    rcases hdich N hNQ hNnorm with hNw | hNQeq
    · exfalso
      apply hidx
      refine (Subgroup.relIndex_dvd_of_le_left Q hNw).trans ?_
      have hsub : N.subgroupOf Q = ψ.ker := by
        rw [hNdef, ← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _
      rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
      exact (Subgroup.card_subgroup_dvd_card _).trans hcardS
    · intro q hq J hJ
      rw [← hNQeq] at hq
      exact ((hmemN q).1 hq).2 J hJ
  intro J hJ
  set K : Subgroup G := Q ⊓ Subgroup.centralizer (J : Set G) with hKdef
  have hKnorm : ∀ g ∈ L, g ^ n.factorial ∈ Subgroup.normalizer (K : Set G) := by
    intro g hg
    have h1 := hLQ (hpowN g hg)
    have h2 := mem_normalizer_centralizer (hpowJ g hg J hJ)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hKdef, Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.1 h1 x, Subgroup.mem_normalizer_iff.1 h2 x]
  rcases hdich K inf_le_left hKnorm with hKw | hKQ
  · have hQN : Q ≤ Subgroup.normalizer (J : Set G) := fun q hq => hQS q hq J hJ
    let χ : Q →* MulAut J := (normalizerToMulAut J).comp (Subgroup.inclusion hQN)
    have hker : χ.ker = K.subgroupOf Q := by
      ext x
      rw [Subgroup.mem_subgroupOf, hKdef, Subgroup.mem_inf]
      simp only [χ, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [← MonoidHom.mem_ker, mem_ker_normalizerToMulAut]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    haveI : Finite (MulAut J) :=
      Finite.of_injective (fun φ : MulAut J => (φ : J → J)) DFunLike.coe_injective
    refine (Subgroup.relIndex_dvd_of_le_left Q hKw).trans ?_
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  · exfalso
    have hJC : J ≤ Subgroup.centralizer (Q : Set G) := by
      rw [← Subgroup.le_centralizer_iff]
      rw [← hKQ]
      exact inf_le_right
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 J))
    have hcard : Nat.card ((P : Subgroup J).map J.subtype) = 3 ^ (Nat.card J).factorization 3 := by
      rw [Subgroup.card_map_of_injective J.subtype_injective, Sylow.card_eq_multiplicity]
    have hf : 2 ≤ (Nat.card J).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by simpa using h9 J hJ)
    have hle := hCQ ((P : Subgroup J).map J.subtype)
      ((Subgroup.map_subtype_le _).trans hJC) (P.isPGroup'.map J.subtype)
    rw [hcard] at hle
    have : 3 ^ 2 ≤ 3 ^ (Nat.card J).factorization 3 := Nat.pow_le_pow_right (by norm_num) hf
    omega

end CFSG.HardMathSupport.MathTwE6
