module

public import CFSG.Goldschmidt.Steps.G37CoreX
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Goldschmidt.Steps.G37Proj

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_normalizer_of_isSylowIn {T L : Subgroup G}
    (hT : CFSG.Open.fusionIsSylowIn 2 T L) :
    Group.IsSolvable (L ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := L ⊓ Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := le_inf hT.1 Subgroup.le_normalizer
  have hTsyl : CFSG.Open.fusionIsSylowIn 2 T N :=
    ⟨hTN, hT.2.1, fun P hPN hP hTP => hT.2.2 P (hPN.trans inf_le_left) hP hTP⟩
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.SStarTransport.exists_sylow_of_isSylowIn hTsyl
  set T' := T.subgroupOf N with hT'
  have hT'n : T'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr inf_le_right
  have hodd : Odd (Nat.card (N ⧸ T')) := by
    rw [← Subgroup.index_eq_card, ← hP]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (P.not_dvd_index))
  have hq : Group.IsSolvable (N ⧸ T') := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hT's : Group.IsSolvable T' := by
    have h2 : IsPGroup 2 T' := hT.2.1.comap_subtype
    have := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range T'.subtype (QuotientGroup.mk' T')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem exists_inner_typeI {M : Type} [Group M] [Finite M] (h31 : S_G31)
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A) {a : M}
    (haA : a ∈ A) {L : Subgroup M} (hL : IsComponentOf L ⊤) (hLK : L ≤ normalClosureIn ⊤ A)
    (hLa : ¬ L ≤ Subgroup.centralizer ({a} : Set M)) :
    ∃ b ∈ A ⊓ L, ∃ c ∈ A ⊓ Subgroup.centralizer (L : Set M), b * c = a ∧
      b ∉ Subgroup.centralizer (L : Set M) ∧
      L ⊓ Subgroup.centralizer ({a} : Set M) = L ⊓ Subgroup.centralizer ({b} : Set M) := by
  obtain ⟨b, hb, c, hc, hbc⟩ := exists_mul_of_mem h31 hO hS hL hLK haA
  have hcL : c ∈ Subgroup.centralizer (L : Set M) := (Subgroup.mem_inf.mp hc).2
  have hcb : c * b = b * c := by
    have := hS.2.1.is_comm.comm ⟨c, (Subgroup.mem_inf.mp hc).1⟩ ⟨b, (Subgroup.mem_inf.mp hb).1⟩
    exact congrArg Subtype.val this
  have hiff : ∀ x ∈ L, x * a = a * x ↔ x * b = b * x := by
    intro x hx
    have hxc : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hcL x hx)
    rw [← hbc]
    constructor
    · intro h
      have h1 : x * b * c = b * x * c := by
        calc x * b * c = x * (b * c) := by group
          _ = b * c * x := h
          _ = b * (c * x) := by group
          _ = b * (x * c) := by rw [hxc]
          _ = b * x * c := by group
      exact mul_right_cancel h1
    · intro h
      calc x * (b * c) = x * b * c := by group
        _ = b * x * c := by rw [h]
        _ = b * (x * c) := by group
        _ = b * (c * x) := by rw [hxc]
        _ = b * c * x := by group
  refine ⟨b, hb, c, hc, hbc, fun hbL => hLa ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hiff x hx).mpr (Subgroup.mem_centralizer_iff.mp hbL x hx)
  · ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, (hiff x hx).mp h⟩, fun ⟨hx, h⟩ => ⟨hx, (hiff x hx).mpr h⟩⟩

section TypeI

variable {L A T : Subgroup G} {b : G}

theorem mem_normalizer_sylow_of_centralizes (hLq : GorensteinWalter.IsQuasisimple L)
    (hT : CFSG.Open.fusionIsSylowIn 2 T L) (hAT : A ≤ T)
    (hAL : ¬ A ≤ Subgroup.centralizer (L : Set G))
    (hmax : ∀ M : Subgroup G, M ≤ L → L ⊓ Subgroup.centralizer ({b} : Set G) ≤ M → M ≠ L →
      M ≤ Subgroup.normalizer (T : Set G))
    (hbZ : b ∉ Subgroup.centralizer (L : Set G)) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgC : g ∈ Subgroup.centralizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) :
      Set G)) :
    g ∈ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.1
  set Tg := T.map (MulAut.conj g).toMonoidHom with hTg
  have hTgL : Tg ≤ L := by
    rintro _ ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgL t).mp (hTL ht)
  have hCbN : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    apply hmax _ inf_le_left le_rfl
    intro h
    apply hbZ
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have : x ∈ L ⊓ Subgroup.centralizer ({b} : Set G) := by rw [h]; exact hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp this).2)
  have hCbNg : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Tg : Set G) := by
    intro x hx
    have hxg : g * x * g⁻¹ = x := by
      rw [(Subgroup.mem_centralizer_iff.mp hgC x hx).symm, mul_inv_cancel_right]
    have h1 : (MulAut.conj g) x ∈ (Subgroup.normalizer (T : Set G)).map
        (MulAut.conj g).toMonoidHom := ⟨x, hCbN hx, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq, MulAut.conj_apply, hxg] at h1
    exact h1
  have hNgL : L ⊓ Subgroup.normalizer (Tg : Set G) ≠ L := by
    intro h
    have hTgn : L ≤ Subgroup.normalizer (Tg : Set G) := h ▸ inf_le_right
    rcases eq_or_le_centralizer_of_le_normalizer hLq hTgL hTgn with h1 | h1
    ·
      have hp : IsPGroup 2 L := h1 ▸ hT.2.1.map _
      have hsolv : Group.IsSolvable L := by
        have := hp.isNilpotent
        infer_instance
      have : Nontrivial L := hLq.1
      have : Group.IsPerfect L := Group.isPerfect_def.mpr hLq.2.1
      exact Group.IsPerfect.not_isSolvable _ hsolv
    · apply hAL
      intro x hx
      have hxT : g * x * g⁻¹ ∈ Tg := ⟨x, hAT hx, rfl⟩
      have h2 := h1 hxT
      rw [Subgroup.mem_centralizer_iff] at h2 ⊢
      intro y hy
      have hy' : g * y * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgL y).mp hy
      have h3 := h2 _ hy'
      have h4 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
        calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h3
          _ = g * (x * y) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h4)
  have hNgT : L ⊓ Subgroup.normalizer (Tg : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    hmax _ inf_le_left (le_inf inf_le_left hCbNg) hNgL
  have hTgT : Tg ≤ Subgroup.normalizer (T : Set G) :=
    fun x hx => hNgT (Subgroup.mem_inf.mpr ⟨hTgL hx, Subgroup.le_normalizer hx⟩)
  have hp : IsPGroup 2 (Tg ⊔ T : Subgroup G) :=
    (hT.2.1.map _).to_sup_of_normal_right' hT.2.1 hTgT
  have h1 : Tg ⊔ T = T := hT.2.2 _ (sup_le hTgL hTL) hp le_sup_right
  have h2 : Tg = T := by
    apply Subgroup.eq_of_le_of_card_ge (h1 ▸ le_sup_left)
    rw [hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_of_map_conj_eq h2

theorem pResidualOf_eq_self_of_perfect {K : Subgroup G} (hK : Group.IsPerfect K) :
    pResidualOf K 2 = K :=
  pResidualOf_eq_self_of_sup (sup_bot_eq K).symm hK (by rw [Subgroup.card_bot]; exact odd_one)

theorem pResidualOf_eq_self_of_odd {Y : Subgroup G} (hY : Odd (Nat.card Y)) :
    pResidualOf Y 2 = Y :=
  pResidualOf_eq_self_of_sup (bot_sup_eq Y).symm inferInstance hY

theorem le_centralizer_of_centralizes_typeI (h33 : S_G33) (hLq : CFSG.Open.IsQuasisimple L)
    (hI : IsGoldTypeI L) (hS : IsSStarIn L A) (hcl : normalClosureIn L A = L)
    (hT : CFSG.Open.fusionIsSylowIn 2 T L) (hAT : A ≤ T)
    (hAL : ¬ A ≤ Subgroup.centralizer (L : Set G))
    (hmax : ∀ M : Subgroup G, M ≤ L → L ⊓ Subgroup.centralizer ({b} : Set G) ≤ M → M ≠ L →
      M ≤ Subgroup.normalizer (T : Set G))
    (hbA : b ∈ A) (hbZ : b ∉ Subgroup.centralizer (L : Set G)) {V : Subgroup G}
    (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (hVC : V ≤ Subgroup.centralizer ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) :
      Set G))
    (hV : Group.IsPerfect V ∨ Odd (Nat.card V)) :
    V ≤ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLq' : GorensteinWalter.IsQuasisimple L := open_isQuasisimple_iff.mp hLq
  have hTL : T ≤ L := hT.1
  have hbT : b ∈ T := hAT hbA
  have hbL : b ∈ L := hTL hbT
  have hVT : V ≤ Subgroup.normalizer (T : Set G) := fun v hv =>
    mem_normalizer_sylow_of_centralizes hLq' hT hAT hAL hmax hbZ (hVL hv) (hVC hv)
  have hbC : b ∈ L ⊓ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hbL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hVres : pResidualOf V 2 = V := by
    rcases hV with h | h
    · exact pResidualOf_eq_self_of_perfect h
    · exact pResidualOf_eq_self_of_odd h
  have hPK : ⁅Subgroup.zpowers b, V⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv
    rw [CFSG.Walter.centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hVC hv) b hbC).symm
  have hCBK : ⁅T ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G), V⁆ = ⊥ := by
    rw [CFSG.Walter.centralizer_zpowers_eq', Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hVC hv)) x
      (Subgroup.mem_inf.mpr ⟨hTL (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩)
  have hVCT : V ≤ Subgroup.centralizer (T : Set G) :=
    CFSG.GorensteinWalter.bender1970_1_1_thompson 2 Nat.prime_two (Subgroup.zpowers b) V T
      (hT.2.1.to_le (Subgroup.zpowers_le.mpr hbT)) hT.2.1 hVres
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hbT)) hVT hPK hCBK
  have hVTC : V ≤ T ⊔ Subgroup.centralizer (L : Set G) := by
    intro v hv
    refine g33_subgroup h33 hLq hI hS hcl hT hAT (hVL hv) ?_ (hVT hv) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hVCT hv)) x (hAT hx)
    · intro t ht
      have h1 : t * v = v * t := (Subgroup.mem_centralizer_iff.mp (hVCT hv)) t ht
      have h2 : v⁻¹ * t * v * t⁻¹ = 1 := by
        rw [mul_assoc v⁻¹, h1]
        group
      rw [h2]
      exact A.one_mem
  have hTN : T ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    hTL.trans (le_normalizer_centralizer L)
  rcases hV with h | h
  · have hTs : Group.IsSolvable T := by
      have := hT.2.1.isNilpotent
      infer_instance
    exact le_of_perfect_of_le_sup h hVTC hTN hTs
  · apply le_of_coprime_of_le_sup hVTC hTN
    obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr h)

end TypeI

section LayerIn

variable {M : Type} [Group M]

@[expose] def layerIn (X L : Subgroup M) : Subgroup M :=
  sSup {K : Subgroup M | IsComponentOf K X ∧ K ≤ L}

theorem layerIn_le (X L : Subgroup M) : layerIn X L ≤ L := sSup_le fun _ hK => hK.2

theorem layerIn_le_X (X L : Subgroup M) : layerIn X L ≤ X := sSup_le fun _ hK => hK.1.1

theorem le_layerIn {X L K : Subgroup M} (hK : IsComponentOf K X) (hKL : K ≤ L) :
    K ≤ layerIn X L := le_sSup ⟨hK, hKL⟩

theorem isPerfect_layerIn (X L : Subgroup M) : Group.IsPerfect (layerIn X L) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (commutator_self_le _) (sSup_le fun K hK => ?_)
  have hK' : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK.1.2.2.2.1)
  rw [← hK']
  exact Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem mem_normalizer_layerIn {X L : Subgroup M} {g : M}
    (hgX : g ∈ Subgroup.normalizer (X : Set M)) (hgL : g ∈ Subgroup.normalizer (L : Set M)) :
    g ∈ Subgroup.normalizer (layerIn X L : Set M) := by
  have key : ∀ g : M, g ∈ Subgroup.normalizer (X : Set M) →
      g ∈ Subgroup.normalizer (L : Set M) → ∀ K ∈ {K : Subgroup M | IsComponentOf K X ∧ K ≤ L},
        K.map (MulAut.conj g).toMonoidHom ∈ {K : Subgroup M | IsComponentOf K X ∧ K ≤ L} := by
    intro g hgX hgL K hK
    refine ⟨CFSG.Walter.isComponentOf_map_conj hK.1 hgX, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgL k).mp (hK.2 hk)
  exact CFSG.Walter.mem_normalizer_sSup_of_map_mem (key g hgX hgL)
    (key g⁻¹ (Subgroup.inv_mem _ hgX) (Subgroup.inv_mem _ hgL))

end LayerIn

section Core

variable {M : Type} [Group M] [Finite M]

variable (h31 : S_G31) (h32Q : S_G32Q) (h33 : S_G33) (hO : goldschmidtOddCore M = ⊥)
  {A : Subgroup M} (hS : IsSStarIn ⊤ A) {a : M} (haA : a ∈ A) {X : Subgroup M}
  (hXa : Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M))
  (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X)) {L : Subgroup M}
  (hL : IsComponentOf L ⊤) (hLK : L ≤ normalClosureIn ⊤ A) (hI : IsGoldTypeI L)
  (hLa : ¬ L ≤ Subgroup.centralizer ({a} : Set M))

include h31 h32Q h33 hO hS haA hXa hXE hL hLK hI hLa

theorem typeI_component {K : Subgroup M} (hK : IsComponentOf K X) : K = L ∨ ⁅K, L⁆ = ⊥ := by
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab⟩ := exists_inner_typeI h31 hO hS haA hL hLK hLa
  obtain ⟨hSL, hcl, -⟩ := componentFacts31 h31 hO hS hL hLK
  obtain ⟨T, hT, hAT, -⟩ := hSL.2.2
  have hLq : CFSG.Open.IsQuasisimple L := open_isQuasisimple_iff.mpr hL.2.2
  obtain ⟨hmax, -⟩ := g32Q_subgroup h32Q hLq hI (isPGroup_center hO hL) hSL hT hAT hb hbZ
  have hAL : ¬ A ⊓ L ≤ Subgroup.centralizer (L : Set M) := not_inf_le_centralizer h31 hO hS hL hLK
  have hXL : X ≤ Subgroup.normalizer (L : Set M) :=
    le_normalizer_component h31 hO hS haA hXa hXE hL hLK
  have hCaX : L ⊓ Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M) :=
    inf_le_right.trans hXa
  by_cases hKL : K ≤ L
  · left
    set E := layerIn X L with hE
    have hEN : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (E : Set M) := by
      intro g hg
      rw [← hCab] at hg
      exact mem_normalizer_layerIn (hCaX hg) (Subgroup.le_normalizer (Subgroup.mem_inf.mp hg).1)
    by_cases hM : L ⊓ Subgroup.normalizer (E : Set M) = L
    · have hLE : L ≤ Subgroup.normalizer (E : Set M) := hM ▸ inf_le_right
      rcases eq_or_le_centralizer_of_le_normalizer hL.2.2 (layerIn_le X L) hLE with h | h
      · have hLX : IsComponentOf L X := isComponentOf_of_le hL (h ▸ layerIn_le_X X L) le_top
        exact eq_of_isComponentOf_of_le hK hLX hKL
      · exact absurd ((le_layerIn hK hKL).trans h |>.trans (Subgroup.centralizer_le hKL))
          (not_le_centralizer_self hK.2.2)
    · exfalso
      have h1 := hmax _ inf_le_left (le_inf inf_le_left hEN) hM
      have hEs : Group.IsSolvable E := by
        have h2 : E ≤ L ⊓ Subgroup.normalizer (T : Set M) :=
          le_inf (layerIn_le X L) (fun x hx => h1 (Subgroup.mem_inf.mpr
            ⟨layerIn_le X L hx, Subgroup.le_normalizer hx⟩))
        have := isSolvable_inf_normalizer_of_isSylowIn hT
        exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h2)
      have : Group.IsPerfect E := isPerfect_layerIn X L
      have hEne : Nontrivial E := by
        rw [Subgroup.nontrivial_iff_ne_bot]
        intro hE0
        apply (Subgroup.nontrivial_iff_ne_bot K).mp hK.2.2.1
        exact le_bot_iff.mp (hE0 ▸ le_layerIn hK hKL)
      exact Group.IsPerfect.not_isSolvable _ hEs
  · right
    rcases le_commutator_or_commutator_eq_bot hK hCaX with h | h
    · exfalso
      apply hKL
      refine h.trans ?_
      rw [Subgroup.commutator_le]
      intro k hk ℓ hℓ
      rw [commutatorElement_def]
      have hℓL := (Subgroup.mem_inf.mp hℓ).1
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXL (hK.1 hk)) ℓ).mp hℓL)
        (L.inv_mem hℓL)
    · have hKC : K ≤ Subgroup.centralizer
          ((L ⊓ Subgroup.centralizer ({b} : Set M) : Subgroup M) : Set M) := by
        rw [← hCab]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have h2 := le_centralizer_of_centralizes_typeI h33 hLq hI hSL hcl hT hAT hAL hmax hb hbZ
        (hK.1.trans hXL) hKC (Or.inl (Group.isPerfect_def.mpr hK.2.2.2.1))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h2

theorem typeI_oddFit :
    oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (L : Set M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, c, hc, hbc, hbZ, hCab⟩ := exists_inner_typeI h31 hO hS haA hL hLK hLa
  obtain ⟨hSL, hcl, -⟩ := componentFacts31 h31 hO hS hL hLK
  obtain ⟨T, hT, hAT, -⟩ := hSL.2.2
  have hLq : CFSG.Open.IsQuasisimple L := open_isQuasisimple_iff.mpr hL.2.2
  obtain ⟨hmax, hcent⟩ := g32Q_subgroup h32Q hLq hI (isPGroup_center hO hL) hSL hT hAT hb hbZ
  have hAL : ¬ A ⊓ L ≤ Subgroup.centralizer (L : Set M) := not_inf_le_centralizer h31 hO hS hL hLK
  have hXL : X ≤ Subgroup.normalizer (L : Set M) :=
    le_normalizer_component h31 hO hS haA hXa hXE hL hLK
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have hYX : Y ≤ X := oddFit_le X
  have hYodd : Odd (Nat.card Y) := odd_card_oddFit X
  have hCaY : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (Y : Set M) := by
    rw [← hCab]
    exact inf_le_right.trans (hXa.trans (normalizer_le_normalizer_oddFit X))
  set YL := Y ⊓ L with hYL
  have hYLodd : Odd (Nat.card YL) := hYodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hYLN : L ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (YL : Set M) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hCaY hg, Subgroup.le_normalizer (Subgroup.mem_inf.mp hg).1⟩)
  have hYL1 : YL = ⊥ := by
    by_cases hM : L ⊓ Subgroup.normalizer (YL : Set M) = L
    · have hLN : L ≤ Subgroup.normalizer (YL : Set M) := hM ▸ inf_le_right
      rcases eq_or_le_centralizer_of_le_normalizer hL.2.2 inf_le_right hLN with h | h
      · exfalso
        have h2 := CFSG.Walter.IsQuasisimple.two_dvd_card hL.2.2
        rw [← h] at h2
        exact (Nat.not_even_iff_odd.mpr hYLodd) (even_iff_two_dvd.mpr h2)
      · have hZ := isPGroup_center hO hL
        have h2 : IsPGroup 2 (L ⊓ Subgroup.centralizer (L : Set M) : Subgroup M) := by
          have h3 : L ⊓ Subgroup.centralizer (L : Set M) = (Subgroup.center L).map L.subtype := by
            ext x
            constructor
            · intro hx
              obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
              exact ⟨⟨x, hxL⟩, (mem_center_iff_mem_centralizer ⟨x, hxL⟩).mpr hxC, rfl⟩
            · rintro ⟨y, hy, rfl⟩
              exact Subgroup.mem_inf.mpr ⟨y.2, (mem_center_iff_mem_centralizer y).mp hy⟩
          rw [h3]
          exact hZ.map _
        have h4 : YL ≤ L ⊓ Subgroup.centralizer (L : Set M) := le_inf inf_le_right h
        have h5 := inf_eq_bot_of_odd_of_isPGroup hYLodd h2
        rw [inf_eq_left.mpr h4] at h5
        exact h5
    · have h1 := hmax _ inf_le_left (le_inf inf_le_left hYLN) hM
      have hYLT : YL ≤ Subgroup.normalizer (T : Set M) := fun x hx =>
        h1 (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, Subgroup.le_normalizer hx⟩)
      have hTC : T ⊓ Subgroup.centralizer ({b} : Set M) ≤ Subgroup.normalizer (YL : Set M) :=
        fun x hx => hYLN (Subgroup.mem_inf.mpr ⟨hT.1 (Subgroup.mem_inf.mp hx).1,
          (Subgroup.mem_inf.mp hx).2⟩)
      have hcomm : ⁅YL, T ⊓ Subgroup.centralizer ({b} : Set M)⁆ ≤ YL ⊓ T := by
        rw [Subgroup.commutator_le]
        intro y hy t ht
        rw [commutatorElement_def]
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have : t * y⁻¹ * t⁻¹ ∈ YL :=
            (Subgroup.mem_normalizer_iff.mp (hTC ht) y⁻¹).mp (YL.inv_mem hy)
          rw [show y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) by group]
          exact YL.mul_mem hy this
        · have htT := (Subgroup.mem_inf.mp ht).1
          exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYLT hy) t).mp htT) (T.inv_mem htT)
      rw [inf_eq_bot_of_odd_of_isPGroup hYLodd hT.2.1, le_bot_iff] at hcomm
      have hYLC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hYLT' : YL ≤ T := fun x hx => hcent (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_inf.mp hx).2, hYLT hx⟩, hYLC hx⟩)
      have h5 := inf_eq_bot_of_odd_of_isPGroup hYLodd hT.2.1
      rwa [inf_eq_left.mpr hYLT'] at h5
  have hYC : Y ≤ Subgroup.centralizer
      ((L ⊓ Subgroup.centralizer ({b} : Set M) : Subgroup M) : Set M) := by
    have hcomm : ⁅Y, L ⊓ Subgroup.centralizer ({b} : Set M)⁆ ≤ YL := by
      rw [Subgroup.commutator_le]
      intro y hy g hg
      rw [commutatorElement_def]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have : g * y⁻¹ * g⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hCaY hg) y⁻¹).mp (Y.inv_mem hy)
        rw [show y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) by group]
        exact Y.mul_mem hy this
      · have hgL := (Subgroup.mem_inf.mp hg).1
        exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXL (hYX hy)) g).mp hgL)
          (L.inv_mem hgL)
    rw [hYL1, le_bot_iff] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact le_centralizer_of_centralizes_typeI h33 hLq hI hSL hcl hT hAT hAL hmax hb hbZ
    (hYX.trans hXL) hYC (Or.inr hYodd)

end Core

end CFSG.Goldschmidt.G37
