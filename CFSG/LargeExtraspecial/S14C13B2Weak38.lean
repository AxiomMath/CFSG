module

public import CFSG.LargeExtraspecial.S14C13B2Weak
public import CFSG.LargeExtraspecial.S3bThirteen

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup

variable {O : Type*} [Group O] [Finite O]

theorem exists_mem_normalizer_not_mem_of_lt_two {P S₀ : Subgroup O} (hP : IsPGroup 2 P)
    (hlt : S₀ < P) : ∃ x ∈ P, x ∉ S₀ ∧ x ∈ normalizer (S₀ : Set O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' : S₀.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ S₀.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt')
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S₀ : Set O)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact mem_subgroupOf.mp hy

namespace WeakSetting

variable {X : Subgroup O} {t : O} {N : Subgroup O} (W : WeakSetting X t N)
include W

omit [Finite O] in
theorem isPGroup : IsPGroup 2 N := fun x => ⟨2, by
  apply Subtype.ext
  simpa using W.pow_four_eq_one x.2⟩

omit [Finite O] in
theorem mem_normalizer {h : O} (hX : h ∈ X) (ht : h * t = t * h) :
    h ∈ normalizer (N : Set O) := by
  rw [mem_normalizer_iff]
  intro n
  constructor
  · exact W.N_norm h hX ht n
  · intro hn
    have ht' : h⁻¹ * t = t * h⁻¹ := by
      calc h⁻¹ * t = h⁻¹ * (t * h) * h⁻¹ := by group
        _ = h⁻¹ * (h * t) * h⁻¹ := by rw [ht]
        _ = t * h⁻¹ := by group
    have := W.N_norm h⁻¹ (inv_mem hX) ht' _ hn
    simpa [mul_assoc] using this

omit W [Finite O] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup O} {g : O}
    (hg : g ∈ normalizer (H : Set O)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  constructor
  · intro h
    have := (mem_normalizer_iff.mp hg _).mp h
    simpa [mul_assoc] using this
  · intro h
    exact (mem_normalizer_iff.mp hg _).mpr (by simpa [mul_assoc] using h)

omit [Finite O] in
theorem map_conj_eq_of_conj_eq {a b : O} (ha : a ∈ X) (hb : b ∈ X)
    (hab : a * t * a⁻¹ = b * t * b⁻¹) :
    N.map (MulAut.conj a).toMonoidHom = N.map (MulAut.conj b).toMonoidHom := by
  have hc : b⁻¹ * a * t = t * (b⁻¹ * a) := by
    calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹) * a := by group
      _ = b⁻¹ * (b * t * b⁻¹) * a := by rw [hab]
      _ = t * (b⁻¹ * a) := by group
  have hn := W.mem_normalizer (mul_mem (inv_mem hb) ha) hc
  ext y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : a⁻¹ * y * a = (b⁻¹ * a)⁻¹ * (b⁻¹ * y * b) * (b⁻¹ * a) := by group
  rw [e]
  constructor
  · intro h
    have := (mem_normalizer_iff.mp hn _).mp h
    simpa [mul_assoc] using this
  · intro h
    have := (mem_normalizer_iff.mp (inv_mem hn) _).mp h
    rwa [inv_inv] at this

theorem mem_map_conj_of_conj_mem {k : O} (hk : k ∈ X) (hxN : k * t * k⁻¹ ∈ N)
    (hne : k * t * k⁻¹ ≠ t) : t ∈ N.map (MulAut.conj k).toMonoidHom := by
  classical
  have T := W.conj hk
  set x := k * t * k⁻¹ with hxdef
  set Nx := N.map (MulAut.conj k).toMonoidHom with hNx
  have hx1 : x ≠ 1 := T.t1
  have htx : t * x = x * t := (W.N_comm x hxN).symm
  set F := N ⊓ centralizer ({x} : Set O) with hF
  have hFN : F ≤ N := inf_le_left
  have hFi : F.relIndex N = 2 := W.relIndex_centralizer_eq_two hxN hx1 hne
  have htF : t ∈ F := ⟨W.t_mem_N, mem_centralizer_singleton_iff.mpr htx⟩
  have hxF : x ∈ F := ⟨hxN, mem_centralizer_singleton_iff.mpr rfl⟩
  set C := X ⊓ centralizer ({t} : Set O) ⊓ centralizer ({x} : Set O) with hC
  have hFC : F ≤ C := fun f hf => ⟨⟨W.N_le hf.1, mem_centralizer_singleton_iff.mpr
    (W.N_comm f hf.1)⟩, hf.2⟩
  have hfin : {P : Subgroup O | F ≤ P ∧ P ≤ C ∧ IsPGroup 2 P}.Finite := Set.toFinite _
  obtain ⟨S₀, hFS₀, hS₀max⟩ :=
    hfin.exists_le_maximal (a := F) ⟨le_rfl, hFC, W.isPGroup.to_le hFN⟩
  have hS₀C : S₀ ≤ C := hS₀max.prop.2.1
  have hS₀2 : IsPGroup 2 S₀ := hS₀max.prop.2.2
  have hmax : ∀ P : Subgroup O, S₀ ≤ P → P ≤ C → IsPGroup 2 P → P = S₀ := fun P h1 h2 h3 =>
    (hS₀max.eq_of_le ⟨hFS₀.trans h1, h2, h3⟩ h1).symm
  have hS₀X : ∀ s ∈ S₀, s ∈ X := fun s hs => (hS₀C hs).1.1
  have htc : ∀ s ∈ S₀, t * s = s * t := fun s hs =>
    (mem_centralizer_singleton_iff.mp (hS₀C hs).1.2).symm
  have hxc : ∀ s ∈ S₀, x * s = s * x := fun s hs =>
    (mem_centralizer_singleton_iff.mp (hS₀C hs).2).symm
  have htS₀ : t ∈ S₀ := hFS₀ htF
  have hxS₀ : x ∈ S₀ := hFS₀ hxF
  have hZ : ∀ y ∈ S₀, (∀ s ∈ S₀, y * s = s * y) → y * y = 1 →
      y = 1 ∨ y = t ∨ y = x ∨ y = x * t := by
    intro y hyS hyc hyy
    have hyN := W.mem_of_sq_eq_one_of_commute hFN hFi (hS₀X y hyS) hyy
      fun f hf => hyc f (hFS₀ hf)
    exact W.mem_centralizer_centralizer hxN hx1 hne hyN fun b hb hbx =>
      hyc b (hFS₀ ⟨hb, mem_centralizer_singleton_iff.mpr hbx⟩)
  have hnorm : ∀ n ∈ normalizer (S₀ : Set O), ∀ a ∈ S₀, (∀ s ∈ S₀, a * s = s * a) →
      a * a = 1 → a ≠ 1 → n * a * n⁻¹ = t ∨ n * a * n⁻¹ = x ∨ n * a * n⁻¹ = x * t := by
    intro n hn a haS hac haa ha1
    have h1 : n * a * n⁻¹ ∈ S₀ := (mem_normalizer_iff.mp hn a).mp haS
    have h2 : ∀ s ∈ S₀, n * a * n⁻¹ * s = s * (n * a * n⁻¹) := by
      intro s hs
      have hs' : n⁻¹ * s * n ∈ S₀ := by
        rw [mem_normalizer_iff.mp hn]
        convert hs using 1
        group
      calc n * a * n⁻¹ * s = n * (a * (n⁻¹ * s * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * s * n) * a) * n⁻¹ := by rw [hac _ hs']
        _ = s * (n * a * n⁻¹) := by group
    have h3 : n * a * n⁻¹ * (n * a * n⁻¹) = 1 := by
      calc n * a * n⁻¹ * (n * a * n⁻¹) = n * (a * a) * n⁻¹ := by group
        _ = 1 := by rw [haa]; group
    have h4 : n * a * n⁻¹ ≠ 1 := fun h => ha1 (by
      calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
    rcases hZ _ h1 h2 h3 with h | h | h | h
    · exact absurd h h4
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨v, hvN, hvX, hvt, hvx⟩ : ∃ v ∈ normalizer (S₀ : Set O), v ∈ X ∧
      v * t * v⁻¹ = t ∧ v * x * v⁻¹ = x * t := by
    have hS₀N : S₀ ≤ normalizer (N : Set O) := fun s hs =>
      W.mem_normalizer (hS₀X s hs) (htc s hs).symm
    have hP : IsPGroup 2 (S₀ ⊔ N : Subgroup O) :=
      hS₀2.to_sup_of_normal_right' W.isPGroup hS₀N
    have hlt : S₀ < S₀ ⊔ N := by
      refine lt_of_le_of_ne le_sup_left fun h => ?_
      have hcomm : ∀ y ∈ N, x * y = y * x := fun y hy => by
        have hy' : y ∈ S₀ ⊔ N := mem_sup_right hy
        rw [← h] at hy'
        exact hxc y hy'
      rcases W.center x hxN hcomm with h' | h'
      · exact hx1 h'
      · exact hne h'
    obtain ⟨v, hvP, hvS, hvN⟩ := exists_mem_normalizer_not_mem_of_lt_two hP hlt
    have hle : S₀ ⊔ N ≤ X ⊓ centralizer ({t} : Set O) := sup_le (fun s hs => (hS₀C hs).1)
      fun n hn => ⟨W.N_le hn, mem_centralizer_singleton_iff.mpr (W.N_comm n hn)⟩
    have hvX : v ∈ X := (hle hvP).1
    have hvt' : v * t = t * v := mem_centralizer_singleton_iff.mp (hle hvP).2
    have hvt : v * t * v⁻¹ = t := by rw [hvt']; group
    refine ⟨v, hvN, hvX, hvt, ?_⟩
    rcases hnorm v hvN x hxS₀ hxc T.tt hx1 with h | h | h
    · exact absurd (by
        calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
          _ = v⁻¹ * (v * t * v⁻¹) * v := by rw [h, hvt]
          _ = t := by group) hne
    · exfalso
      have hvC : v ∈ C := by
        refine ⟨⟨hvX, mem_centralizer_singleton_iff.mpr hvt'⟩,
          mem_centralizer_singleton_iff.mpr ?_⟩
        calc v * x = v * x * v⁻¹ * v := by group
          _ = x * v := by rw [h]
      have hle' : S₀ ⊔ zpowers v ≤ S₀ ⊔ N := sup_le le_sup_left (zpowers_le.mpr hvP)
      have heq := hmax (S₀ ⊔ zpowers v) le_sup_left (sup_le hS₀C (zpowers_le.mpr hvC))
        (hP.to_le hle')
      exact hvS (heq ▸ (le_sup_right : zpowers v ≤ S₀ ⊔ zpowers v) (mem_zpowers v))
    · exact h
  by_contra htNx
  obtain ⟨u, huN, huX, hux, hut⟩ : ∃ u ∈ normalizer (S₀ : Set O), u ∈ X ∧
      u * x * u⁻¹ = x ∧ u * t * u⁻¹ = x * t := by
    have hS₀N : S₀ ≤ normalizer (Nx : Set O) := fun s hs =>
      T.mem_normalizer (hS₀X s hs) (hxc s hs).symm
    have hP : IsPGroup 2 (S₀ ⊔ Nx : Subgroup O) :=
      hS₀2.to_sup_of_normal_right' T.isPGroup hS₀N
    have hlt : S₀ < S₀ ⊔ Nx := by
      refine lt_of_le_of_ne le_sup_left fun h => htNx ?_
      refine T.mem_of_commute W.t_mem fun y hy => ?_
      have hy' : y ∈ S₀ ⊔ Nx := mem_sup_right hy
      rw [← h] at hy'
      exact htc y hy'
    obtain ⟨u, huP, huS, huN⟩ := exists_mem_normalizer_not_mem_of_lt_two hP hlt
    have hle : S₀ ⊔ Nx ≤ X ⊓ centralizer ({x} : Set O) := sup_le
      (fun s hs => ⟨(hS₀C hs).1.1, (hS₀C hs).2⟩)
      fun n hn => ⟨T.N_le hn, mem_centralizer_singleton_iff.mpr (T.N_comm n hn)⟩
    have huX : u ∈ X := (hle huP).1
    have hux' : u * x = x * u := mem_centralizer_singleton_iff.mp (hle huP).2
    have hux : u * x * u⁻¹ = x := by rw [hux']; group
    refine ⟨u, huN, huX, hux, ?_⟩
    rcases hnorm u huN t htS₀ htc W.tt W.t1 with h | h | h
    · exfalso
      have huC : u ∈ C := by
        refine ⟨⟨huX, mem_centralizer_singleton_iff.mpr ?_⟩,
          mem_centralizer_singleton_iff.mpr hux'⟩
        calc u * t = u * t * u⁻¹ * u := by group
          _ = t * u := by rw [h]
      have hle' : S₀ ⊔ zpowers u ≤ S₀ ⊔ Nx := sup_le le_sup_left (zpowers_le.mpr huP)
      have heq := hmax (S₀ ⊔ zpowers u) le_sup_left (sup_le hS₀C (zpowers_le.mpr huC))
        (hP.to_le hle')
      exact huS (heq ▸ (le_sup_right : zpowers u ≤ S₀ ⊔ zpowers u) (mem_zpowers u))
    · exact absurd (show t = x by
        calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
          _ = u⁻¹ * (u * x * u⁻¹) * u := by rw [h, hux]
          _ = x := by group).symm hne
    · exact h
  have hg'N : v * u ∈ normalizer (S₀ : Set O) := mul_mem hvN huN
  have hg't : (v * u) * t * (v * u)⁻¹ = x := by
    calc (v * u) * t * (v * u)⁻¹ = v * (u * t * u⁻¹) * v⁻¹ := by group
      _ = (v * x * v⁻¹) * (v * t * v⁻¹) := by rw [hut]; group
      _ = x := by rw [hvx, hvt, mul_assoc, W.tt, mul_one]
  have hNx' : Nx = N.map (MulAut.conj (v * u)).toMonoidHom :=
    W.map_conj_eq_of_conj_eq hk (mul_mem hvX huX) hg't.symm
  have hQS : N ⊓ S₀ = F :=
    le_antisymm (fun y hy => ⟨hy.1, mem_centralizer_singleton_iff.mpr (hxc y hy.2).symm⟩)
      (le_inf hFN hFS₀)
  have hinj : Function.Injective (MulAut.conj (v * u)).toMonoidHom :=
    (MulAut.conj (v * u)).injective
  have hidx : (Nx ⊓ S₀).relIndex Nx = 2 := by
    rw [hNx', ← map_conj_eq_of_mem_normalizer hg'N, ← map_inf_eq _ _ _ hinj,
      relIndex_map_map_of_injective _ _ hinj, hQS]
    exact hFi
  exact htNx (T.mem_of_sq_eq_one_of_commute inf_le_left hidx W.t_mem W.tt
    fun f hf => htc f hf.2)

theorem exists_swap {k : O} (hk : k ∈ X) (hxN : k * t * k⁻¹ ∈ N) (hne : k * t * k⁻¹ ≠ t) :
    ∃ u ∈ X, u * t * u⁻¹ = k * t * k⁻¹ ∧ u * (k * t * k⁻¹) * u⁻¹ = t := by
  have T := W.conj hk
  set x := k * t * k⁻¹ with hxdef
  have hx1 : x ≠ 1 := T.t1
  have htx : t * x = x * t := (W.N_comm x hxN).symm
  have htNx := W.mem_map_conj_of_conj_mem hk hxN hne
  obtain ⟨a, ha, hat⟩ := W.exists_comm_eq_t hxN hx1 hne
  have h1z : a * t * a⁻¹ = t := by rw [W.N_comm a ha]; group
  have h1t : a * x * a⁻¹ = x * t := by
    calc a * x * a⁻¹ = a * x * a⁻¹ * x⁻¹ * x := by group
      _ = x * t := by rw [hat, htx]
  obtain ⟨b, hb, hbt⟩ := T.exists_comm_eq_t htNx W.t1 (Ne.symm hne)
  have h2z : b * t * b⁻¹ = x * t := by
    calc b * t * b⁻¹ = b * t * b⁻¹ * t⁻¹ * t := by group
      _ = x * t := by rw [hbt]
  have h2t : b * x * b⁻¹ = x := by rw [T.N_comm b hb]; group
  obtain ⟨u, hu, hut, hux⟩ := sigma3_of_transvections (H := X) W.tt T.tt htx (W.N_le ha)
    (T.N_le hb) h1z h1t h2z h2t x (by simp) t (by simp) hne
  exact ⟨u, hu, hut, hux⟩

omit [Finite O] in
theorem eq_of_commute_of_sq {y : O} (hyN : y ∈ N) (hy1 : y ≠ 1) (hyt : y ≠ t)
    {S₀ : Subgroup O} (hFS₀ : N ⊓ centralizer ({y} : Set O) ≤ S₀) {w : O} (hwX : w ∈ X)
    (hw : ∀ s ∈ S₀, w * s = s * w) (hww : w * w = 1) :
    w = 1 ∨ w = t ∨ w = y ∨ w = y * t := by
  have hwN := W.mem_of_sq_eq_one_of_commute inf_le_left
    (W.relIndex_centralizer_eq_two hyN hy1 hyt) hwX hww fun f hf => hw f (hFS₀ hf)
  exact W.mem_centralizer_centralizer hyN hy1 hyt hwN fun b hb hby =>
    hw b (hFS₀ ⟨hb, mem_centralizer_singleton_iff.mpr hby⟩)

theorem exists_maximal_twoSubgroup (y : O) :
    ∃ S₀ : Subgroup O, N ⊓ centralizer ({y} : Set O) ≤ S₀ ∧
      S₀ ≤ X ⊓ centralizer ({t} : Set O) ⊓ centralizer ({y} : Set O) ∧ IsPGroup 2 S₀ ∧
      ∀ P : Subgroup O, S₀ ≤ P →
        P ≤ X ⊓ centralizer ({t} : Set O) ⊓ centralizer ({y} : Set O) → IsPGroup 2 P →
        P = S₀ := by
  set F := N ⊓ centralizer ({y} : Set O)
  have hfin : {P : Subgroup O | F ≤ P ∧
      P ≤ X ⊓ centralizer ({t} : Set O) ⊓ centralizer ({y} : Set O) ∧ IsPGroup 2 P}.Finite :=
    Set.toFinite _
  obtain ⟨S₀, hFS₀, hS₀max⟩ := hfin.exists_le_maximal (a := F)
    ⟨le_rfl, fun f hf => ⟨⟨W.N_le hf.1, mem_centralizer_singleton_iff.mpr (W.N_comm f hf.1)⟩,
      hf.2⟩, W.isPGroup.to_le inf_le_left⟩
  exact ⟨S₀, hFS₀, hS₀max.prop.2.1, hS₀max.prop.2.2, fun P h1 h2 h3 =>
    (hS₀max.eq_of_le ⟨hFS₀.trans h1, h2, h3⟩ h1).symm⟩

theorem maximal_of_not_conj {y : O} (hyN : y ∈ N) (hy1 : y ≠ 1) (hyt : y ≠ t)
    (hyc : ∀ h ∈ X, h * t * h⁻¹ ≠ y) {S₀ : Subgroup O}
    (hFS₀ : N ⊓ centralizer ({y} : Set O) ≤ S₀)
    (hS₀ : S₀ ≤ X ⊓ centralizer ({t} : Set O) ⊓ centralizer ({y} : Set O))
    (hmax : ∀ P : Subgroup O, S₀ ≤ P →
      P ≤ X ⊓ centralizer ({t} : Set O) ⊓ centralizer ({y} : Set O) → IsPGroup 2 P → P = S₀) :
    ∀ P : Subgroup O, S₀ ≤ P → P ≤ X ⊓ centralizer ({y} : Set O) → IsPGroup 2 P → P = S₀ := by
  intro P hS₀P hPC hP
  by_contra hne
  obtain ⟨n, hnP, hnS₀, hnN⟩ :=
    exists_mem_normalizer_not_mem_of_lt_two hP (lt_of_le_of_ne hS₀P (Ne.symm hne))
  have hnX : n ∈ X := (hPC hnP).1
  have hny : n * y = y * n := mem_centralizer_singleton_iff.mp (hPC hnP).2
  have hw : ∀ s ∈ S₀, n * t * n⁻¹ * s = s * (n * t * n⁻¹) := by
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S₀ := by
      refine (mem_normalizer_iff.mp hnN (n⁻¹ * s * n)).mpr ?_
      rw [show n * (n⁻¹ * s * n) * n⁻¹ = s by group]
      exact hs
    have htc : t * (n⁻¹ * s * n) = n⁻¹ * s * n * t :=
      (mem_centralizer_singleton_iff.mp (hS₀ hs').1.2).symm
    calc n * t * n⁻¹ * s = n * (t * (n⁻¹ * s * n)) * n⁻¹ := by group
      _ = n * (n⁻¹ * s * n * t) * n⁻¹ := by rw [htc]
      _ = s * (n * t * n⁻¹) := by group
  have hww : n * t * n⁻¹ * (n * t * n⁻¹) = 1 := by
    calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [W.tt]; group
  have hwX : n * t * n⁻¹ ∈ X := mul_mem (mul_mem hnX W.t_mem) (inv_mem hnX)
  rcases W.eq_of_commute_of_sq hyN hy1 hyt hFS₀ hwX hw hww with h | h | h | h
  · apply W.t1
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · have hnt : n * t = t * n := by
      calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [h]
    have hle : S₀ ⊔ zpowers n ≤ P := sup_le hS₀P (zpowers_le.mpr hnP)
    have heq := hmax (S₀ ⊔ zpowers n) le_sup_left
      (sup_le hS₀ (zpowers_le.mpr ⟨⟨hnX, mem_centralizer_singleton_iff.mpr hnt⟩,
        mem_centralizer_singleton_iff.mpr hny⟩)) (hP.to_le hle)
    exact hnS₀ (heq ▸ (le_sup_right : zpowers n ≤ S₀ ⊔ zpowers n) (mem_zpowers n))
  · apply hyt
    calc y = n⁻¹ * (n * y) := by group
      _ = n⁻¹ * y * n := by rw [hny]; group
      _ = n⁻¹ * (n * t * n⁻¹) * n := by rw [h]
      _ = t := by group
  · obtain ⟨a, ha, hat⟩ := W.exists_comm_eq_t hyN hy1 hyt
    have hay : a * y * a⁻¹ = y * t := by
      calc a * y * a⁻¹ = a * y * a⁻¹ * y⁻¹ * y := by group
        _ = t * y := by rw [hat]
        _ = y * t := (W.N_comm y hyN).symm
    refine hyc (a⁻¹ * n) (mul_mem (inv_mem (W.N_le ha)) hnX) ?_
    calc (a⁻¹ * n) * t * (a⁻¹ * n)⁻¹ = a⁻¹ * (n * t * n⁻¹) * a := by group
      _ = a⁻¹ * (a * y * a⁻¹) * a := by rw [h, hay]
      _ = y := by group

theorem janko {y k : O} (hyN : y ∈ N) (hy1 : y ≠ 1) (hyt : y ≠ t)
    (hyc : ∀ h ∈ X, h * t * h⁻¹ ≠ y) (hk : k ∈ X) (hky : k * y * k⁻¹ ∈ N) :
    ∃ m ∈ X, m * t = t * m ∧ m * y * m⁻¹ = k * y * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_one_or_eq_of_mem_zpowers W.tt (W.sq y hyN) with hy2 | hy2
  swap
  ·
    refine ⟨k, hk, ?_, rfl⟩
    have h1 : (k * y * k⁻¹) * (k * y * k⁻¹) = k * t * k⁻¹ := by rw [← hy2]; group
    rcases eq_one_or_eq_of_mem_zpowers W.tt (W.sq _ hky) with h | h
    · exfalso
      rw [h] at h1
      apply W.t1
      calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
        _ = 1 := by rw [← h1]; group
    · rw [h] at h1
      calc k * t = k * t * k⁻¹ * k := by group
        _ = t * k := by rw [← h1]
  set y' := k * y * k⁻¹ with hy'
  have hy'1 : y' ≠ 1 := fun h => hy1 (by
    calc y = k⁻¹ * y' * k := by rw [hy']; group
      _ = 1 := by rw [h]; group)
  have hy'c : ∀ h ∈ X, h * t * h⁻¹ ≠ y' := fun h hh e => hyc (k⁻¹ * h)
    (mul_mem (inv_mem hk) hh) (by
      calc (k⁻¹ * h) * t * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * t * h⁻¹) * k := by group
        _ = y := by rw [e, hy']; group)
  have hy't : y' ≠ t := fun e => hy'c 1 (one_mem _) (by rw [e]; group)
  obtain ⟨S₀, hFS₀, hS₀, hS₀2, hS₀max⟩ := W.exists_maximal_twoSubgroup y
  obtain ⟨S₁, hFS₁, hS₁, hS₁2, hS₁max⟩ := W.exists_maximal_twoSubgroup y'
  have hmax₀ := W.maximal_of_not_conj hyN hy1 hyt hyc hFS₀ hS₀ hS₀max
  have hmax₁ := W.maximal_of_not_conj hky hy'1 hy't hy'c hFS₁ hS₁ hS₁max
  set P' := S₁.map (MulAut.conj k⁻¹).toMonoidHom with hP'
  have hP'C : P' ≤ X ⊓ centralizer ({y} : Set O) := by
    rintro _ ⟨s, hs, rfl⟩
    have hsX : s ∈ X := (hS₁ hs).1.1
    have hsy : s * y' = y' * s := mem_centralizer_singleton_iff.mp (hS₁ hs).2
    have e : (MulAut.conj k⁻¹).toMonoidHom s = k⁻¹ * s * k := by simp
    rw [e]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hk) hsX) hk,
      mem_centralizer_singleton_iff.mpr ?_⟩
    calc k⁻¹ * s * k * y = k⁻¹ * (s * y') * k := by rw [hy']; group
      _ = k⁻¹ * (y' * s) * k := by rw [hsy]
      _ = y * (k⁻¹ * s * k) := by rw [hy']; group
  have hP'2 : IsPGroup 2 P' := hS₁2.map _
  have hP'max : ∀ R : Subgroup O, P' ≤ R → R ≤ X ⊓ centralizer ({y} : Set O) →
      IsPGroup 2 R → R = P' := by
    intro R hP'R hRC hR
    have h1 : R.map (MulAut.conj k).toMonoidHom = S₁ := by
      refine hmax₁ _ ?_ ?_ (hR.map _)
      · intro s hs
        refine ⟨k⁻¹ * s * k⁻¹⁻¹, hP'R ⟨s, hs, rfl⟩, ?_⟩
        simp [mul_assoc]
      · rintro _ ⟨r, hr, rfl⟩
        have hrX : r ∈ X := (hRC hr).1
        have h2 : r * y = y * r := mem_centralizer_singleton_iff.mp (hRC hr).2
        have e : (MulAut.conj k).toMonoidHom r = k * r * k⁻¹ := by simp
        rw [e]
        refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hrX) (inv_mem hk),
          mem_centralizer_singleton_iff.mpr ?_⟩
        calc k * r * k⁻¹ * y' = k * (r * y) * k⁻¹ := by rw [hy']; group
          _ = k * (y * r) * k⁻¹ := by rw [h2]
          _ = y' * (k * r * k⁻¹) := by rw [hy']; group
    rw [hP', ← h1, Subgroup.map_map]
    ext r
    simp [mul_assoc]
  have hS₀K : S₀ ≤ X ⊓ centralizer ({y} : Set O) := fun s hs => ⟨(hS₀ hs).1.1, (hS₀ hs).2⟩
  obtain ⟨c, hcC, hcP⟩ := exists_mem_map_conj_eq_of_maximal (K := X ⊓ centralizer ({y} : Set O))
    hS₀K hS₀2 hmax₀ hP'C hP'2 hP'max
  have hcX : c ∈ X := hcC.1
  have hcy : c * y * c⁻¹ = y := by
    rw [mem_centralizer_singleton_iff.mp hcC.2]
    group
  set k' := c * k⁻¹ with hk'
  have hk'X : k' ∈ X := mul_mem hcX (inv_mem hk)
  have hk'y : k' * y' * k'⁻¹ = y := by
    rw [hk', hy', show c * k⁻¹ * (k * y * k⁻¹) * (c * k⁻¹)⁻¹ = c * y * c⁻¹ by group, hcy]
  have htS₁ : t ∈ S₁ := hFS₁ ⟨W.t_mem_N, mem_centralizer_singleton_iff.mpr
    (W.N_comm y' hky).symm⟩
  have hwS₀ : ∀ s ∈ S₀, k' * t * k'⁻¹ * s = s * (k' * t * k'⁻¹) := by
    intro s hs
    rw [← hcP] at hs
    obtain ⟨_, ⟨s₁, hs₁, rfl⟩, rfl⟩ := hs
    have htc : t * s₁ = s₁ * t := (mem_centralizer_singleton_iff.mp (hS₁ hs₁).1.2).symm
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k' * t * k'⁻¹ * (c * (k⁻¹ * s₁ * k⁻¹⁻¹) * c⁻¹) = k' * (t * s₁) * k'⁻¹ := by
          rw [hk']; group
      _ = k' * (s₁ * t) * k'⁻¹ := by rw [htc]
      _ = c * (k⁻¹ * s₁ * k⁻¹⁻¹) * c⁻¹ * (k' * t * k'⁻¹) := by rw [hk']; group
  have hww : k' * t * k'⁻¹ * (k' * t * k'⁻¹) = 1 := by
    calc k' * t * k'⁻¹ * (k' * t * k'⁻¹) = k' * (t * t) * k'⁻¹ := by group
      _ = 1 := by rw [W.tt]; group
  have hwX : k' * t * k'⁻¹ ∈ X := mul_mem (mul_mem hk'X W.t_mem) (inv_mem hk'X)
  have hk't : k' * t = t * k' := by
    rcases W.eq_of_commute_of_sq hyN hy1 hyt hFS₀ hwX hwS₀ hww with h | h | h | h
    · exfalso
      apply W.t1
      calc t = k'⁻¹ * (k' * t * k'⁻¹) * k' := by group
        _ = 1 := by rw [h]; group
    · calc k' * t = k' * t * k'⁻¹ * k' := by group
        _ = t * k' := by rw [h]
    · exact absurd h (hyc k' hk'X)
    · exfalso
      obtain ⟨a, ha, hat⟩ := W.exists_comm_eq_t hyN hy1 hyt
      have hay : a * y * a⁻¹ = y * t := by
        calc a * y * a⁻¹ = a * y * a⁻¹ * y⁻¹ * y := by group
          _ = t * y := by rw [hat]
          _ = y * t := (W.N_comm y hyN).symm
      refine hyc (a⁻¹ * k') (mul_mem (inv_mem (W.N_le ha)) hk'X) ?_
      calc (a⁻¹ * k') * t * (a⁻¹ * k')⁻¹ = a⁻¹ * (k' * t * k'⁻¹) * a := by group
        _ = a⁻¹ * (a * y * a⁻¹) * a := by rw [h, hay]
        _ = y := by group
  refine ⟨k'⁻¹, inv_mem hk'X, ?_, ?_⟩
  · calc k'⁻¹ * t = k'⁻¹ * (t * k') * k'⁻¹ := by group
      _ = k'⁻¹ * (k' * t) * k'⁻¹ := by rw [hk't]
      _ = t * k'⁻¹ := by group
  · rw [← hk'y]
    group

end WeakSetting

end CFSG.LargeExtraspecial.S14
