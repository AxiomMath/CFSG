module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.UnipotentFixedPoints
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.StrongEmbeddingD2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RelIndexPrime

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {X : Type} [Group X] [Finite X]

theorem nine_le_card_inf_centralizer {N : Subgroup X} (hN : IsElemAbelian 3 N)
    (hNcard : 3 ^ 4 ≤ Nat.card N) {x : X} (hx : x ∈ Subgroup.normalizer (N : Set X))
    (hx3 : x ^ 3 = 1) : 9 ≤ Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) := by
  have hcomm : ∀ a b : N, a * b = b * a := isMulCommutative_iff.mp hN.1
  let _ : CommGroup N := { (inferInstance : Group N) with mul_comm := hcomm }
  let σ : N →* N :=
    { toFun := fun n => ⟨x * n * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx n).mp n.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  have hσ : ∀ a, σ (σ (σ a)) = a := by
    intro a
    apply Subtype.ext
    show x * (x * (x * (a : X) * x⁻¹) * x⁻¹) * x⁻¹ = a
    have hx3' : x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx3
    have : x * (x * (x * (a : X) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * (a : X) * (x * x * x)⁻¹ := by
      group
    rw [this, hx3']; simp
  have hexp : ∀ a : N, a ^ 3 = 1 := fun a => Subtype.ext (hN.2 a a.2)
  have h81 := hNcard.trans (card_le_card_ker_pow_three σ hσ hexp)
  set ψ : N →* N := MonoidHom.id N * σ⁻¹ with hψ
  have hker : Nat.card ψ.ker = Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨((k : N) : X), (k : N).2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun k => rfl
        right_inv := fun y => rfl }
    ·
      have hk : (k : N) * (σ (k : N))⁻¹ = 1 := k.2
      have h1 : σ (k : N) = (k : N) := by
        have := congrArg (· * σ (k : N)) hk
        simpa using this.symm
      have h2 : x * ((k : N) : X) * x⁻¹ = ((k : N) : X) := congrArg Subtype.val h1
      show ((k : N) : X) ∈ Subgroup.centralizer ({x} : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      calc h * ((k : N) : X) = (h * ((k : N) : X) * h⁻¹) * h := by group
        _ = ((k : N) : X) * h := by rw [h2]
    ·
      have h2 := Subgroup.mem_centralizer_iff.mp y.2.2 x (Set.mem_singleton x)
      have h3 : σ ⟨y.1, y.2.1⟩ = ⟨y.1, y.2.1⟩ := by
        apply Subtype.ext
        show x * (y : X) * x⁻¹ = (y : X)
        calc x * (y : X) * x⁻¹ = ((x * (y : X)) * x⁻¹) := rfl
          _ = (y : X) * x * x⁻¹ := by rw [h2]
          _ = (y : X) := by group
      show (⟨y.1, y.2.1⟩ : N) * (σ ⟨y.1, y.2.1⟩)⁻¹ = 1
      rw [h3]; simp
  rw [← hker]
  by_contra hlt
  have hlt : Nat.card ψ.ker < 9 := not_le.mp hlt
  have hNp : IsPGroup 3 N := fun y => ⟨1, Subtype.ext (by simpa using hN.2 y y.2)⟩
  have hkp : IsPGroup 3 ψ.ker := hNp.to_subgroup _
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).mp hkp
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
  rw [hj] at h81
  have h27 : (3 ^ j) ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left this 3
  omega

omit [Finite X] in
theorem mem_normalizer_of_normal_subgroupOf {P N : Subgroup X} (hNP : N ≤ P)
    (hNn : (N.subgroupOf P).Normal) {x : X} (hxP : x ∈ P) :
    x ∈ Subgroup.normalizer (N : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ (y : X) (hy : y ∈ P) (n : X), n ∈ N → y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    have := hNn.conj_mem ⟨n, hNP hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.mp this
  constructor
  · exact hconj x hxP h
  · intro hh
    have hhP : h ∈ P := by
      have h1 : x * h * x⁻¹ ∈ P := hNP hh
      have := P.mul_mem (P.mul_mem (P.inv_mem hxP) h1) hxP
      simpa [mul_assoc] using this
    have := hconj x⁻¹ (P.inv_mem hxP) _ hh
    simpa [mul_assoc] using this

theorem three_le_pRank_inf_centralizer_of_normal {P N : Subgroup X} (hNP : N ≤ P)
    (hNn : (N.subgroupOf P).Normal) (hN : IsElemAbelian 3 N) (hNcard : 3 ^ 4 ≤ Nat.card N)
    {x : X} (hxP : x ∈ P) (hx : orderOf x = 3) :
    3 ≤ pRank 3 (P ⊓ Subgroup.centralizer ({x} : Set X)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  by_cases hxN : x ∈ N
  · have hle : N ≤ P ⊓ Subgroup.centralizer ({x} : Set X) := by
      refine le_inf hNP ?_
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := isMulCommutative_iff.mp hN.1 ⟨h, hxN⟩ ⟨n, hn⟩
      exact congrArg Subtype.val this
    have hNp : IsPGroup 3 N := fun y => ⟨1, Subtype.ext (by simpa using hN.2 y y.2)⟩
    obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 3)).mp hNp
    have h4 : 4 ≤ r := by
      by_contra hlt
      have : 3 ^ r ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (by omega : 3 ≤ 4).trans (h4.trans ((le_pRank_of_isElemAbelian hp hN hr).trans
      (pRank_mono 3 hp hle)))
  · have hxnorm : x ∈ Subgroup.normalizer (N : Set X) :=
      mem_normalizer_of_normal_subgroupOf hNP hNn hxP
    set C : Subgroup X := N ⊓ Subgroup.centralizer ({x} : Set X) with hC
    have h9 : 9 ≤ Nat.card C := nine_le_card_inf_centralizer hN hNcard hxnorm hx3
    have hNp : IsPGroup 3 N := fun y => ⟨1, Subtype.ext (by simpa using hN.2 y y.2)⟩
    have hCp : IsPGroup 3 C := hNp.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp hCp
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k ≤ 1 := by omega
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have hdvd : 3 ^ 2 ∣ Nat.card C := by
      rw [hk]; exact pow_dvd_pow 3 hk2
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := C) (n := 2) hdvd
    set E₂ : Subgroup X := K.map C.subtype with hE₂
    have hE₂card : Nat.card E₂ = 9 := by
      rw [hE₂, Subgroup.card_map_of_injective C.subtype_injective, hK]; norm_num
    have hE₂C : E₂ ≤ C := Subgroup.map_subtype_le K
    have hE₂N : E₂ ≤ N := hE₂C.trans inf_le_left
    have hE₂cent : ∀ r ∈ E₂, x * r = r * x := fun r hr =>
      Subgroup.mem_centralizer_iff.mp (hE₂C hr).2 x (Set.mem_singleton x)
    set P' : Subgroup X := Subgroup.zpowers x with hP'
    have hP'card : Nat.card P' = 3 := by rw [hP', Nat.card_zpowers, hx]
    have hP'cent : ∀ p ∈ P', ∀ r ∈ E₂, p * r = r * p := by
      intro p hp' r hr
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp'
      exact (Commute.zpow_left (show Commute x r from hE₂cent r hr) m).eq
    have hP'cube : ∀ p ∈ P', p ^ 3 = 1 := by
      intro p hp'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp'
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hinf : P' ⊓ E₂ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      have hyo : orderOf y = 3 := orderOf_eq_prime (hP'cube y hy.1) hy1
      have hzp : Subgroup.zpowers y = P' := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy.1) ?_
        rw [hP'card, Nat.card_zpowers, hyo]
      have hxy : x ∈ Subgroup.zpowers y := by rw [hzp]; exact Subgroup.mem_zpowers x
      exact hxN (Subgroup.zpowers_le.mpr (hE₂N hy.2) hxy)
    have hnormE₂ : P' ≤ Subgroup.normalizer (E₂ : Set X) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have : x * h * x⁻¹ = h := by
          calc x * h * x⁻¹ = h * x * x⁻¹ := by rw [hE₂cent h hh]
            _ = h := by group
        rw [this]; exact hh
      · intro hh
        have h1 := hE₂cent _ hh
        have h2 : h = x * h * x⁻¹ := by
          calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
            _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [← h1]
            _ = x * h * x⁻¹ := by group
        rw [h2]; exact hh
    have hfac : ∀ z ∈ P' ⊔ E₂, ∃ p ∈ P', ∃ r ∈ E₂, z = p * r := by
      intro z hz
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P' E₂ hnormE₂,
        Set.mem_mul] at hz
      obtain ⟨p, hp', r, hr, rfl⟩ := hz
      exact ⟨p, hp', r, hr, rfl⟩
    have hrel := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.relIndex_sup_eq_three_of_mul
      hP'card hinf hfac
    set E : Subgroup X := P' ⊔ E₂ with hE
    have hE₂E : E₂ ≤ E := le_sup_right
    have hEcard : Nat.card E = 3 ^ 3 := by
      have h1 := Subgroup.card_mul_index (E₂.subgroupOf E)
      have h2 : Nat.card (E₂.subgroupOf E) = Nat.card E₂ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂E).toEquiv
      have h3 : (E₂.subgroupOf E).index = 3 := hrel
      rw [h2, h3, hE₂card] at h1
      rw [← h1]; norm_num
    have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      obtain ⟨p, hp', r, hr, rfl⟩ := hfac a ha
      obtain ⟨q, hq', s, hs, rfl⟩ := hfac b hb
      have hpq : Commute p q := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp'
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq'
        exact (Commute.refl x).zpow_zpow m n
      have hps : Commute p s := hP'cent p hp' s hs
      have hrq : Commute r q := (hP'cent q hq' r hr).symm
      have hrs : Commute r s :=
        congrArg Subtype.val (isMulCommutative_iff.mp hN.1 ⟨r, hE₂N hr⟩ ⟨s, hE₂N hs⟩)
      exact (Commute.mul_left (Commute.mul_right hpq hps) (Commute.mul_right hrq hrs)).eq
    have hEe : IsElemAbelian 3 E := by
      refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hEcomm a a.2 b b.2), ?_⟩
      intro a ha
      obtain ⟨p, hp', r, hr, rfl⟩ := hfac a ha
      have hpr : Commute p r := hP'cent p hp' r hr
      rw [hpr.mul_pow, hP'cube p hp', hN.2 r (hE₂N hr), one_mul]
    have hEle : E ≤ P ⊓ Subgroup.centralizer ({x} : Set X) := by
      refine sup_le ?_ ?_
      · refine le_inf (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr ?_)
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        rfl
      · exact le_inf (hE₂N.trans hNP) ((hE₂C).trans inf_le_right)
    exact (le_pRank_of_isElemAbelian hp hEe hEcard).trans (pRank_mono 3 hp hEle)

@[expose] def KFactNormalRankFourThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup X), IsPGroup 3 P → 4 ≤ pRank 3 P →
    ∃ N : Subgroup X, N ≤ P ∧ (N.subgroupOf P).Normal ∧ IsElemAbelian 3 N ∧
      3 ^ 4 ≤ Nat.card N

omit [Finite X] in
theorem map_conj_inf_centralizer {M : Subgroup X} {m x : X} (hm : m ∈ M) :
    (M ⊓ Subgroup.centralizer ({x} : Set X)).map (MulAut.conj m).toMonoidHom =
      M ⊓ Subgroup.centralizer ({m * x * m⁻¹} : Set X) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, ⟨hzM, hz⟩, rfl⟩
    refine ⟨M.mul_mem (M.mul_mem hm hzM) (M.inv_mem hm), ?_⟩
    calc m * x * m⁻¹ * (m * z * m⁻¹) = m * (x * z) * m⁻¹ := by group
      _ = m * (z * x) * m⁻¹ := by rw [hz]
      _ = m * z * m⁻¹ * (m * x * m⁻¹) := by group
  · rintro ⟨hyM, hy⟩
    refine ⟨m⁻¹ * y * m, ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) hyM) hm, ?_⟩, by group⟩
    have : m * x * m⁻¹ * y = y * (m * x * m⁻¹) := hy
    calc x * (m⁻¹ * y * m) = m⁻¹ * (m * x * m⁻¹ * y) * m := by group
      _ = m⁻¹ * (y * (m * x * m⁻¹)) * m := by rw [this]
      _ = m⁻¹ * y * m * x := by group

variable {G : Type} [Group G] [Finite G]

theorem D2Escape.pure_of_normalRankFour (hK : KFactNormalRankFourThree) {P : Sylow 3 G}
    {M A H R : Subgroup G} (h : D2Escape 3 P M A H R) (h3 : 3 ∈ GLBBetaFour G) :
    ∀ x ∈ M, orderOf x = 3 → 3 ≤ pRank 3 (M ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have h4 : 4 ≤ pRank 3 (P : Subgroup G) := by
    rw [pRank_sylow_eq_globalRank 3 hp P]
    exact betaFour_globalRank h3
  obtain ⟨N, hNP, hNn, hN, hNcard⟩ := hK G (P : Subgroup G) P.isPGroup' h4
  intro x hxM hx
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]; simp
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le 3 P h.sylow_le
    (Subgroup.zpowers_le.mpr hxM) hzp
  have hx'P : (m : G) * x * (m : G)⁻¹ ∈ (P : Subgroup G) :=
    hm ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply]⟩
  have hx'o : orderOf ((m : G) * x * (m : G)⁻¹) = 3 := by
    have := orderOf_injective (MulAut.conj (m : G)).toMonoidHom (MulAut.conj (m : G)).injective x
    rw [hx] at this
    simpa [MulAut.conj_apply] using this
  have hpure := three_le_pRank_inf_centralizer_of_normal hNP hNn hN hNcard hx'P hx'o
  have hle : (P : Subgroup G) ⊓ Subgroup.centralizer ({(m : G) * x * (m : G)⁻¹} : Set G) ≤
      M ⊓ Subgroup.centralizer ({(m : G) * x * (m : G)⁻¹} : Set G) :=
    inf_le_inf_right _ h.sylow_le
  have hmap := map_conj_inf_centralizer (M := M) (x := x) m.2
  have hrank := pRank_map_of_injective 3 hp (MulAut.conj (m : G)).toMonoidHom
    (MulAut.conj (m : G)).injective (M ⊓ Subgroup.centralizer ({x} : Set G))
  rw [hmap] at hrank
  exact hpure.trans ((pRank_mono 3 hp hle).trans hrank.le)

theorem D2Escape.stronglyEmbedded_of_normalRankFour (hK : KFactNormalRankFourThree)
    {P : Sylow 3 G} {M A H R : Subgroup G} (h : D2Escape 3 P M A H R) (hglob : D2Global G)
    (h3 : 3 ∈ GLBBetaFour G) : GLBStronglyEmbedded 3 M :=
  D2Escape.stronglyEmbedded_of_pure h hglob h3 (D2Escape.pure_of_normalRankFour hK h h3)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
