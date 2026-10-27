module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Eight
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Lay
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
theorem conjClosure_conjClosure_of_gen (hgen : conjClosure Y G ⊔ T = G) (hTG : T ≤ G)
    (hTY : ∀ t ∈ T, ∀ y ∈ Y, t * y = y * t) :
    conjClosure Y (conjClosure Y G) = conjClosure Y G := by
  set N := conjClosure Y G with hN
  have hGN : G ≤ Subgroup.normalizer (N : Set (MulAut V)) := le_normalizer_conjClosure
  have key : ∀ t ∈ T, ∀ x ∈ conjClosure Y N, t * x * t⁻¹ ∈ conjClosure Y N := by
    intro t ht x hx
    unfold conjClosure at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, y, hy, rfl⟩ := hx
      have htg : t * g * t⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hGN (hTG ht)) g).mp hg
      have e : t * (g * y * g⁻¹) * t⁻¹ = (t * g * t⁻¹) * y * (t * g * t⁻¹)⁻¹ := by
        have : t * y * t⁻¹ = y := by rw [hTY t ht y hy]; group
        calc t * (g * y * g⁻¹) * t⁻¹ = (t * g * t⁻¹) * (t * y * t⁻¹) * (t * g * t⁻¹)⁻¹ := by group
          _ = (t * g * t⁻¹) * y * (t * g * t⁻¹)⁻¹ := by rw [this]
      rw [e]
      exact Subgroup.subset_closure ⟨_, htg, y, hy, rfl⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  have hle : N ⊔ T ≤ Subgroup.normalizer (conjClosure Y N : Set (MulAut V)) := by
    refine sup_le le_normalizer_conjClosure fun t ht => ?_
    exact mem_normalizer_of_conj_mem (key t ht) (fun x hx => by
      simpa using key t⁻¹ (T.inv_mem ht) x hx)
  rw [hgen] at hle
  apply le_antisymm (conjClosure_le le_conjClosure)
  have hgens : ∀ g ∈ G, ∀ y ∈ Y, g * y * g⁻¹ ∈ conjClosure Y N := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hle hg) y).mp (le_conjClosure hy)
  exact (Subgroup.closure_le _).mpr (by
    rintro _ ⟨g, hg, y, hy, rfl⟩
    exact hgens g hg y hy)

theorem pCore_two_eq_bot_of_normal {N : Subgroup (MulAut V)} (hNG : N ≤ G)
    (hNn : (N.subgroupOf G).Normal) (h : pCore 2 ↥G = ⊥) : pCore 2 ↥N = ⊥ := by
  have h1 : (pCore 2 ↥(N.subgroupOf G)).map (N.subgroupOf G).subtype ≤ pCore 2 ↥G :=
    map_pCore_le_pCore_of_isSubnormal' hNn.isSubnormal
  rw [h, le_bot_iff] at h1
  have h2 : pCore 2 ↥(N.subgroupOf G) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have h3 := pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hNG)
  rw [h2, Subgroup.map_bot] at h3
  exact h3.symm

omit [Finite V] in
theorem centralizes_of_forall_component (hYG : Y ≤ G)
    (hno : ∀ L : Subgroup ↥G, CFSG.IsComponent L → ∀ (y : MulAut V) (hy : y ∈ Y), ∀ l ∈ L,
      l * ⟨y, hYG hy⟩ = ⟨y, hYG hy⟩ * l)
    {L : Subgroup ↥G} (hL : CFSG.IsComponent L) {x : MulAut V} (hx : x ∈ conjClosure Y G) :
    (⟨x, conjClosure_le hYG hx⟩ : ↥G) ∈ Subgroup.centralizer (L : Set ↥G) := by
  have hP : conjClosure Y G ≤ (Subgroup.centralizer (L : Set ↥G)).map G.subtype := by
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    refine mem_map_subtype_mul hg (hYG hy) _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hL' := isComponent_map_conj hL (⟨g, hg⟩ : ↥G)⁻¹
    have hl₁ : (⟨g, hg⟩ : ↥G)⁻¹ * l * ⟨g, hg⟩ ∈ L.map (MulAut.conj (⟨g, hg⟩ : ↥G)⁻¹).toMonoidHom :=
      mem_map_conj_iff.mpr (by
        have e : ((⟨g, hg⟩ : ↥G)⁻¹)⁻¹ * ((⟨g, hg⟩ : ↥G)⁻¹ * l * ⟨g, hg⟩) *
            (⟨g, hg⟩ : ↥G)⁻¹ = l := by
          group
        rw [e]
        exact hl)
    have h1 := hno _ hL' y hy _ hl₁
    calc l * (⟨g, hg⟩ * ⟨y, hYG hy⟩ * ⟨g, hg⟩⁻¹)
        = ⟨g, hg⟩ * ((⟨g, hg⟩⁻¹ * l * ⟨g, hg⟩) * ⟨y, hYG hy⟩) * ⟨g, hg⟩⁻¹ := by group
      _ = ⟨g, hg⟩ * (⟨y, hYG hy⟩ * (⟨g, hg⟩⁻¹ * l * ⟨g, hg⟩)) * ⟨g, hg⟩⁻¹ := by rw [h1]
      _ = (⟨g, hg⟩ * ⟨y, hYG hy⟩ * ⟨g, hg⟩⁻¹) * l := by group
  obtain ⟨n, hn, hnx⟩ := hP hx
  have : n = ⟨x, conjClosure_le hYG hx⟩ := Subtype.ext hnx
  rwa [← this]


theorem Emb5Cfg.exists_component (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1)
    (hself : (Y.subgroupOf G).IsSubnormal → Lift5 G Y Y) :
    ∃ (L : Subgroup ↥G) (y : MulAut V) (hy : y ∈ Y) (l : ↥G), CFSG.IsComponent L ∧ l ∈ L ∧
      l * ⟨y, (cfg.adm.hYC hy).1⟩ ≠ ⟨y, (cfg.adm.hYC hy).1⟩ * l := by
  by_contra hno'
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hno : ∀ L : Subgroup ↥G, CFSG.IsComponent L → ∀ (y : MulAut V) (hy : y ∈ Y), ∀ l ∈ L,
      l * ⟨y, hYG hy⟩ = ⟨y, hYG hy⟩ * l := by
    intro L hL y hy l hl
    by_contra hne
    exact hno' ⟨L, y, hy, l, hL, hl, hne⟩
  have hTY : ∀ t ∈ T, ∀ y ∈ Y, t * y = y * t := fun t ht y hy =>
    ((Subgroup.mem_centralizer_iff.mp (cfg.adm.le_centralizer ht)) y hy).symm
  set N := conjClosure Y G with hN
  have hNG : N ≤ G := conjClosure_le hYG
  have hGN : G ≤ Subgroup.normalizer (N : Set (MulAut V)) := le_normalizer_conjClosure
  have hNn : (N.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).2 le_normalizer_conjClosure
  have hlayer : CFSG.layer ↥N = ⊥ :=
    layer_eq_bot (Subgroup.inclusion hNG) (Subgroup.inclusion_injective hNG)
      (by rw [Subgroup.inclusion_range]; exact hNn) fun L hL a l hl =>
        (Subgroup.mem_centralizer_iff.mp (centralizes_of_forall_component hYG hno hL a.2) l hl).symm
  have hO2 : pCore 2 ↥N = ⊥ := pCore_two_eq_bot_of_normal hNG hNn cfg.o2
  obtain ⟨M', hMc, hMcop, hFM⟩ := exists_fitting_decomp (X := ↥N) hO2
  have hMn : ∀ g ∈ Subgroup.normalizer (N : Set (MulAut V)), ∀ x ∈ M'.map N.subtype,
      g * x * g⁻¹ ∈ M'.map N.subtype := fun g hg x hx =>
    conj_mem_map_of_characteristic' hg hx
  have hF : CFSG.generalizedFitting ↥N = pCore 3 ↥N ⊔ (M'.map N.subtype).subgroupOf N := by
    have h1 : (M'.map N.subtype).subgroupOf N = M' :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective M'
    rw [h1]
    show fittingSubgroup ↥N ⊔ CFSG.layer ↥N = _
    rw [hlayer, sup_bot_eq, hFM]
  have hcop : Nat.Coprime (Nat.card ↥(M'.map N.subtype)) 6 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hMcop
  have hQ := CFSG.CGT.PushingUpLit.CGT6E.emb55F_holds V G T Y N (M'.map N.subtype)
    (cfg.sec5 hV) hNG le_conjClosure
    (conjClosure_conjClosure_of_gen cfg.gen cfg.adm.hTG hTY)
    (cfg.adm.hTG.trans hGN) (Subgroup.map_subtype_le _)
    (fun h hh n hn => hMn h (Subgroup.le_normalizer hh) n hn)
    (fun t ht => mem_normalizer_of_conj_mem (hMn t (hGN (cfg.adm.hTG ht)))
      (fun x hx => by simpa using hMn t⁻¹ (hGN (G.inv_mem (cfg.adm.hTG ht))) x hx)) hcop hF
  set Q : Subgroup (MulAut V) := (pCore 3 ↥N).map N.subtype with hQdef
  have hQG : Q ≤ G := (Subgroup.map_subtype_le _).trans hNG
  have hQn : (Q.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQG).2 fun g hg =>
      mem_normalizer_of_conj_mem (fun x hx => conj_mem_map_of_characteristic' (hGN hg) hx)
        (fun x hx => by
          have h := conj_mem_map_of_characteristic' (X := N) (D := pCore 3 ↥N)
            (hGN (G.inv_mem hg)) hx
          rwa [inv_inv] at h)
  have hQ3 : IsPGroup 3 ↥Q := (pCore_isPGroup (p := 3) (G := ↥N)).map N.subtype
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYQ : (Y.subgroupOf Q).IsSubnormal :=
    CFSG.GorensteinWalter.isSubnormal_of_nilpotent hQ3.isNilpotent Y hQ
  exact cfg.nolift ⟨Y, hself (CFSG.GroupTheory.isSubnormal_subgroupOf_trans hQ hQG hYQ
    hQn.isSubnormal)⟩

end CFSG.CGT.PushingUpLit.CGT6
