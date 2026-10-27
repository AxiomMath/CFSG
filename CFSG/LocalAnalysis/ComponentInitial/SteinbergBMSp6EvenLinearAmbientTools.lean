module

public import CFSG.RankThree.Transfer.FixedPoints
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBM

open Subgroup

variable {G : Type} [Group G]

theorem card_centralizer_conj (w f : G) :
    Nat.card (centralizer ({w * f * w⁻¹} : Set G)) = Nat.card (centralizer ({f} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨w⁻¹ * c * w, ?_⟩
      invFun := fun c => ⟨w * c * w⁻¹, ?_⟩
      left_inv := fun c => Subtype.ext (by dsimp only; group)
      right_inv := fun c => Subtype.ext (by dsimp only; group) }
  · have h := mem_centralizer_singleton_iff.1 c.2
    rw [mem_centralizer_singleton_iff]
    calc w⁻¹ * c * w * f = w⁻¹ * (c * (w * f * w⁻¹)) * w := by group
      _ = w⁻¹ * ((w * f * w⁻¹) * c) * w := by rw [h]
      _ = f * (w⁻¹ * c * w) := by group
  · have h := mem_centralizer_singleton_iff.1 c.2
    rw [mem_centralizer_singleton_iff]
    calc w * c * w⁻¹ * (w * f * w⁻¹) = w * (c * f) * w⁻¹ := by group
      _ = w * (f * c) * w⁻¹ := by rw [h]
      _ = w * f * w⁻¹ * (w * c * w⁻¹) := by group

theorem card_inf_centralizer_conj {C : Subgroup G} {x : G} (hx : x ∈ normalizer (C : Set G))
    (M : Set G) :
    Nat.card ↥(C ⊓ centralizer ((fun m => x * m * x⁻¹) '' M)) =
      Nat.card ↥(C ⊓ centralizer M) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨x⁻¹ * c * x, ?_⟩
      invFun := fun c => ⟨x * c * x⁻¹, ?_⟩
      left_inv := fun c => Subtype.ext (by dsimp only; group)
      right_inv := fun c => Subtype.ext (by dsimp only; group) }
  · obtain ⟨hcC, hcM⟩ := mem_inf.1 c.2
    refine mem_inf.2 ⟨(mem_set_normalizer_iff''.1 hx _).1 hcC, ?_⟩
    rw [mem_centralizer_iff]
    intro m hm
    have h := (mem_centralizer_iff.1 hcM) (x * m * x⁻¹) ⟨m, hm, rfl⟩
    calc m * (x⁻¹ * c * x) = x⁻¹ * ((x * m * x⁻¹) * c) * x := by group
      _ = x⁻¹ * (c * (x * m * x⁻¹)) * x := by rw [h]
      _ = x⁻¹ * c * x * m := by group
  · obtain ⟨hcC, hcM⟩ := mem_inf.1 c.2
    refine mem_inf.2 ⟨(mem_set_normalizer_iff.1 hx _).1 hcC, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨m, hm, rfl⟩
    have h := (mem_centralizer_iff.1 hcM) m hm
    calc x * m * x⁻¹ * (x * c * x⁻¹) = x * (m * c) * x⁻¹ := by group
      _ = x * (c * m) * x⁻¹ := by rw [h]
      _ = x * c * x⁻¹ * (x * m * x⁻¹) := by group

theorem inf_centralizer_mul {C : Subgroup G} (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c) {c : G}
    (hc : c ∈ C) (y : G) :
    C ⊓ centralizer ({y * c} : Set G) = C ⊓ centralizer ({y} : Set G) := by
  ext d
  simp only [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hd, h⟩
    refine ⟨hd, ?_⟩
    have hdc : d * c = c * d := hCab d hd c hc
    calc d * y = d * (y * c) * c⁻¹ := by group
      _ = y * c * d * c⁻¹ := by rw [h]
      _ = y * (c * d) * c⁻¹ := by group
      _ = y * (d * c) * c⁻¹ := by rw [hdc]
      _ = y * d := by group
  · rintro ⟨hd, h⟩
    refine ⟨hd, ?_⟩
    have hdc : d * c = c * d := hCab d hd c hc
    calc d * (y * c) = d * y * c := by group
      _ = y * d * c := by rw [h]
      _ = y * (d * c) := by group
      _ = y * (c * d) := by rw [hdc]
      _ = y * c * d := by group

theorem card_sup_dvd_of_commute {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) ∣ Nat.card H * Nat.card K := by
  have hc : ∀ (h : H) (k : K), Commute (H.subtype h) (K.subtype k) := fun h k => hHK h h.2 k k.2
  have hr := MonoidHom.noncommCoprod_range H.subtype K.subtype hc
  rw [range_subtype, range_subtype] at hr
  rw [← Nat.card_prod, ← hr]
  exact Subgroup.card_range_dvd _

theorem mem_fixedPoints_zpowers_iff {α : Type*} [MulAction G α] {z : G} {a : α} :
    a ∈ MulAction.fixedPoints (zpowers z) α ↔ z • a = a := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨z, mem_zpowers z⟩
  · intro h g
    have hz : z ∈ MulAction.stabilizer G a := h
    exact (zpowers_le.2 hz) g.2

theorem false_of_transfer_of_not_two_dvd_index [Finite G] (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) {X : Subgroup G} (hX : ¬ 2 ∣ X.index)
    (ξ : X →* Multiplicative (ZMod 2)) {z : G} (hz : orderOf z = 2)
    (hξ : ∀ (g : G) (h : g⁻¹ * z * g ∈ X), ξ ⟨_, h⟩ = Multiplicative.ofAdd 1) : False := by
  classical
  have : Fintype (G ⧸ X) := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hmod := hp.card_modEq_card_fixedPoints (G ⧸ X)
  have hset : MulAction.fixedPoints (zpowers z) (G ⧸ X) = {Xc | z • Xc = Xc} := by
    ext Xc
    exact mem_fixedPoints_zpowers_iff
  have hcard : Nat.card (MulAction.fixedPoints (zpowers z) (G ⧸ X)) =
      Nat.card {Xc : G ⧸ X // z • Xc = Xc} := by
    rw [hset]
    rfl
  have hodd : Nat.card {Xc : G ⧸ X // z • Xc = Xc} % 2 = 1 := by
    rw [← hcard]
    have h1 : Nat.card (G ⧸ X) % 2 = 1 := by
      change X.index % 2 = 1
      omega
    rw [← h1]
    exact hmod.symm
  have hτz : ξ.transfer z = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [CFSG.RankThree.Transfer.transfer_eq_prod_fixed_of_orderOf_lt ξ z ?_]
    · refine (Finset.prod_congr (g := fun Xc : G ⧸ X =>
        Multiplicative.ofAdd (1 : ZMod 2) ^ (if z • Xc = Xc then 1 else 0)) rfl
        fun Xc _ => ?_).trans ?_
      · split_ifs with h
        · rw [pow_one, CFSG.RankThree.Transfer.cosetValue_of_mem ξ
            (CFSG.RankThree.Transfer.smul_eq_self_iff_out.1 h)]
          exact hξ _ _
        · exact (pow_zero _).symm
      · rw [Finset.prod_pow_eq_pow_sum, Finset.sum_boole, Nat.cast_id, ← Fintype.card_subtype,
          ← Nat.card_eq_fintype_card, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
        congr 1
        rw [← ZMod.natCast_mod, hodd, Nat.cast_one]
    · intro h hh
      rw [hz] at hh
      have h1 : orderOf (h : G) = 1 := by
        have := orderOf_pos (h : G)
        omega
      rw [orderOf_eq_one_iff] at h1
      rw [show h = 1 from Subtype.ext h1]
      exact map_one ξ
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hGs ξ.transfer.ker
    (MonoidHom.normal_ker _) with h | h
  · obtain ⟨x, y, hxy⟩ := hGnab
    apply hxy
    have hinj : Function.Injective ξ.transfer := (MonoidHom.ker_eq_bot_iff _).1 h
    apply hinj
    rw [map_mul, map_mul, mul_comm]
  · have hz1 : z ∈ ξ.transfer.ker := by
      rw [h]
      exact mem_top z
    have hz2 : ξ.transfer z = 1 := hz1
    rw [hτz] at hz2
    exact absurd hz2 (by decide)

theorem not_two_dvd_index_normalizer [Finite G] {C : Subgroup G}
    (hC2 : ∀ c ∈ C, c ^ 2 = 1) (hCab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c)
    (huniq : ∀ U : Subgroup G, U ≤ normalizer (C : Set G) → (∀ u ∈ U, u ^ 2 = 1) →
      (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) → Nat.card U = Nat.card C → U = C) :
    ¬ 2 ∣ (normalizer (C : Set G)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalizer (C : Set G) with hXdef
  have hCX : C ≤ X := le_normalizer
  have hconj : ∀ g : G, (∀ c ∈ C, g * c * g⁻¹ ∈ X) → g ∈ X := by
    intro g hg
    set U := C.map (MulAut.conj g).toMonoidHom with hU
    have hUX : U ≤ X := by
      rintro _ ⟨c, hc, rfl⟩
      exact hg c hc
    have hU2 : ∀ u ∈ U, u ^ 2 = 1 := by
      rintro _ ⟨c, hc, rfl⟩
      rw [← map_pow, hC2 c hc, map_one]
    have hUab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul, hCab c hc d hd]
    have hUcard : Nat.card U = Nat.card C :=
      (Nat.card_congr (C.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm
    have hUC := huniq U hUX hU2 hUab hUcard
    rw [hXdef, mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      change g * h * g⁻¹ ∈ C
      rw [← hUC]
      exact ⟨h, hh, rfl⟩
    · intro hh
      change g * h * g⁻¹ ∈ C at hh
      rw [← hUC] at hh
      obtain ⟨c, hc, hch⟩ := hh
      have hch' : g * c * g⁻¹ = g * h * g⁻¹ := hch
      have hceq : c = h := mul_left_cancel (mul_right_cancel hch')
      rw [← hceq]
      exact hc
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  set P := (S : Subgroup X).map X.subtype with hPdef
  have hPp : IsPGroup 2 P := S.isPGroup'.map _
  have hPX : P ≤ X := map_subtype_le _
  have hCp : IsPGroup 2 C := fun c => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hC2 c c.2)⟩
  have hCP : C ≤ P := by
    have hp : IsPGroup 2 (C.subgroupOf X) := hCp.comap_subtype
    have hle := hp.le_sylow_of_normal S
    intro c hc
    exact ⟨⟨c, hCX hc⟩, hle (mem_subgroupOf.2 hc), rfl⟩
  obtain ⟨P', hPP'⟩ := hPp.exists_le_sylow
  have hP'X : (P' : Subgroup G) ≤ X := by
    by_contra hne
    have hlt : P < P' := lt_of_le_of_ne hPP' fun h => hne (h ▸ hPX)
    have : Group.IsNilpotent (P' : Subgroup G) := P'.isPGroup'.isNilpotent
    have hlt' : P.subgroupOf P' < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      rw [subgroupOf_eq_top] at h
      exact hlt.ne' (le_antisymm h hPP')
    obtain ⟨g, hgN, hgP⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt')
    have hgP' : ∀ p ∈ P, (g : G) * p * (g : G)⁻¹ ∈ P := by
      intro p hp
      have h1 := (mem_set_normalizer_iff.1 hgN ⟨p, hPP' hp⟩).1 (mem_subgroupOf.2 hp)
      exact h1
    have hgX : (g : G) ∈ X := hconj g fun c hc => hPX (hgP' c (hCP hc))
    set Q := P ⊔ zpowers (g : G) with hQ
    have hQP' : Q ≤ P' := sup_le hPP' (zpowers_le.2 g.2)
    have hQX : Q ≤ X := sup_le hPX (zpowers_le.2 hgX)
    have hQp : IsPGroup 2 (Q.subgroupOf X) := (P'.isPGroup'.to_le hQP').comap_subtype
    have hSQ : (S : Subgroup X) ≤ Q.subgroupOf X := fun s hs =>
      mem_subgroupOf.2 (le_sup_left (a := P) ⟨s, hs, rfl⟩)
    have hQS := S.is_maximal' hQp hSQ
    have hgS : (⟨g, hgX⟩ : X) ∈ (S : Subgroup X) := by
      rw [← hQS]
      exact mem_subgroupOf.2 (le_sup_right (a := P) (mem_zpowers (g : G)))
    exact hgP (mem_subgroupOf.2 ⟨_, hgS, rfl⟩)
  exact fun h2 => P'.not_dvd_index (h2.trans (index_dvd_of_le hP'X))

theorem two_pow_dvd_card_centralizer [Finite G] {C P : Subgroup G} {u : G} (hu : u ^ 2 = 1)
    (hC2 : ∀ c ∈ C, c ^ 2 = 1) {N m : ℕ} (hP : Nat.card P = 2 ^ N)
    (hPu : ∀ x ∈ P, u⁻¹ * (x * u * x⁻¹) ∈ C)
    (hfix : Nat.card ↥(C ⊓ centralizer {u}) ≤ 2 ^ m) :
    2 ^ (N - m) ∣ Nat.card (centralizer {u}) := by
  classical
  set K := (centralizer {u}).subgroupOf P with hK
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hu])
  have hmem : ∀ x : P, u⁻¹ * ((x : G) * u * (x : G)⁻¹) ∈ C ⊓ centralizer {u} := by
    intro x
    refine Subgroup.mem_inf.2 ⟨hPu x x.2, ?_⟩
    rw [mem_centralizer_singleton_iff, mul_inv_cancel_left]
    set v := (x : G) * u * (x : G)⁻¹ with hv
    have hv2 : v * v = 1 := by
      rw [hv]
      calc (x : G) * u * (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) = (x : G) * (u * u) * (x : G)⁻¹ :=
            by group
        _ = 1 := by rw [← pow_two, hu, mul_one, mul_inv_cancel]
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have hc2 := hC2 _ (hPu x x.2)
    rw [pow_two] at hc2
    have key : u⁻¹ * v * u⁻¹ * v = 1 := by
      rw [hv, ← hc2]
      group
    have h3 : u⁻¹ * v * u⁻¹ = v⁻¹ := eq_inv_of_mul_eq_one_left key
    calc u⁻¹ * v * u = u⁻¹ * v * u⁻¹ * (u * u) := by group
      _ = v := by rw [h3, ← pow_two, hu, mul_one, hvinv]
  have hwd : ∀ x y : P, x⁻¹ * y ∈ K →
      (⟨_, hmem x⟩ : ↥(C ⊓ centralizer {u})) = ⟨_, hmem y⟩ := by
    intro x y hxy
    apply Subtype.ext
    have h := mem_subgroupOf.1 hxy
    rw [mem_centralizer_singleton_iff, Subgroup.coe_mul, Subgroup.coe_inv] at h
    change u⁻¹ * ((x : G) * u * (x : G)⁻¹) = u⁻¹ * ((y : G) * u * (y : G)⁻¹)
    congr 1
    calc (x : G) * u * (x : G)⁻¹ =
        (x : G) * ((x : G)⁻¹ * y * u * ((x : G)⁻¹ * y)⁻¹) * (x : G)⁻¹ := by
          rw [h, mul_inv_cancel_right]
      _ = (y : G) * u * (y : G)⁻¹ := by group
  let f : P ⧸ K → ↥(C ⊓ centralizer {u}) :=
    Quotient.lift (fun x : P => (⟨_, hmem x⟩ : ↥(C ⊓ centralizer {u})))
      fun x y hxy => hwd x y (QuotientGroup.leftRel_apply.mp hxy)
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q₂
    have h' : u⁻¹ * ((x : G) * u * (x : G)⁻¹) = u⁻¹ * ((y : G) * u * (y : G)⁻¹) :=
      congrArg Subtype.val h
    have h'' := mul_left_cancel h'
    rw [QuotientGroup.eq, mem_subgroupOf, mem_centralizer_singleton_iff, Subgroup.coe_mul,
      Subgroup.coe_inv]
    calc (x : G)⁻¹ * y * u = (x : G)⁻¹ * ((y : G) * u * (y : G)⁻¹) * y := by group
      _ = (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * y := by rw [h'']
      _ = u * ((x : G)⁻¹ * y) := by group
  have hle : Nat.card (P ⧸ K) ≤ 2 ^ m := (Nat.card_le_card_of_injective f hf).trans hfix
  have hPK := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have hKdvd : Nat.card K ∣ 2 ^ N := hP ▸ Subgroup.card_subgroup_dvd_card K
  obtain ⟨j, -, hKj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hKdvd
  have hNj : N ≤ m + j := by
    have h1 : 2 ^ N ≤ 2 ^ m * 2 ^ j := by
      rw [← hP, hPK, hKj]
      exact Nat.mul_le_mul_right _ hle
    rw [← pow_add] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hKC : Nat.card K ∣ Nat.card (centralizer {u}) := by
    refine Subgroup.card_dvd_of_injective
      ⟨⟨fun k => ⟨((k : P) : G), k.2⟩, rfl⟩, fun _ _ => rfl⟩ ?_
    intro k₁ k₂ h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  rw [hKj] at hKC
  exact (pow_dvd_pow 2 (by omega)).trans hKC

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
