module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedData3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding

theorem eq_of_sl_subgroup {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X] {R : Sylow p X}
    {X₀ : Subgroup X} {z : X} {E C : Subgroup X} [E.Normal]
    {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}
    (hstr : ReducedStructure3 p R X₀ z E C e) (hzp : orderOf z = p) {F L : Subgroup X}
    (hFR : F ≤ (R : Subgroup X)) (hFcard : Nat.card F = p ^ 3) (hFexp : ∀ x ∈ F, x ^ p = 1)
    (hFZ : (Subgroup.center F).map F.subtype = Subgroup.zpowers z)
    (eF : F ⧸ Subgroup.center F ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (F : Set X))).map (centerQuotientAction F eF)) :
    F = E := by
  have hp := (Fact.out : p.Prime)
  have hNn : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hzE : Subgroup.zpowers z ≤ E := hstr.center_eq ▸ Subgroup.map_subtype_le _
  have hzN : Subgroup.zpowers z ≤ CFSG.pCore p X := hzE.trans hstr.le_pCore
  have hNR : CFSG.pCore p X ≤ (R : Subgroup X) := CFSG.pCore_isPGroup.le_sylow_of_normal R
  have hFN : F ≤ CFSG.pCore p X := by
    rcases inf_le_map_center_or_le_sup_of_normal (Y := CFSG.pCore p X) eF hSL with h1 | h1
    · exfalso
      have hcard1 : Nat.card (F ⊓ CFSG.pCore p X : Subgroup X) ≤ p := by
        have := Subgroup.card_le_of_le (hFZ ▸ h1 : F ⊓ CFSG.pCore p X ≤ Subgroup.zpowers z)
        rwa [Nat.card_zpowers, hzp] at this
      have hmul := card_mul_relIndex_aux (inf_le_left : F ⊓ CFSG.pCore p X ≤ F)
      rw [hFcard] at hmul
      have hrel : (CFSG.pCore p X).relIndex F = (F ⊓ CFSG.pCore p X).relIndex F := by
        rw [inf_comm, Subgroup.inf_relIndex_right]
      have hsup : (CFSG.pCore p X).relIndex (F ⊔ CFSG.pCore p X) =
          (CFSG.pCore p X).relIndex F := Subgroup.relIndex_sup_right F (CFSG.pCore p X)
      have hmr := Subgroup.relIndex_mul_relIndex (CFSG.pCore p X) (F ⊔ CFSG.pCore p X)
        (R : Subgroup X) le_sup_right (sup_le hFR hNR)
      rw [hstr.relIndex_eq, hsup, hrel] at hmr
      have hle : (F ⊓ CFSG.pCore p X).relIndex F ≤ p :=
        Nat.le_of_dvd hp.pos ⟨_, hmr.symm⟩
      have hlow : p ^ 2 ≤ (F ⊓ CFSG.pCore p X).relIndex F := by
        by_contra hlt
        push Not at hlt
        have := Nat.mul_lt_mul_of_le_of_lt hcard1 hlt hp.pos
        nlinarith [pow_pos hp.pos 2]
      nlinarith [hp.two_le]
    · exact h1.trans (sup_le le_rfl (hFZ ▸ hzN))
  have hFE : F ≤ E := by
    intro x hx
    obtain ⟨g, hg, c, hc, rfl⟩ := exists_mul_eq_of_mem_sup_normal (hstr.sup_eq ▸ hFN hx)
    have hcomm : Commute g c := (Subgroup.mem_centralizer_iff.mp (hstr.centralizer_eq ▸ hc) g hg)
    have hpow : c ^ p = 1 := by
      have h1 := hFexp _ hx
      rwa [hcomm.mul_pow, hstr.pow_eq_one g hg, one_mul] at h1
    exact E.mul_mem hg (hzE (hstr.omega_le c hc hpow))
  exact Subgroup.eq_of_le_of_card_ge hFE (by rw [hFcard, hstr.card_eq])

section Lift

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def constrainedQ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (z : G)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) : Subgroup G :=
  ((P.subtype hPC : Subgroup (Subgroup.centralizer ({z} : Set G))) ⊓
    CFSG.Op_p'p p (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype

omit [Finite G] in
theorem mem_constrainedQ_iff {p : ℕ} [Fact p.Prime] {P : Sylow p G} {z : G}
    {hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)} {g : G}
    (hg : g ∈ (P : Subgroup G)) :
    g ∈ constrainedQ p P z hPC ↔ QuotientGroup.mk' (primeComplementCore p) ⟨g, hPC hg⟩ ∈
      CFSG.pCore p (ReducedCentralizer p z) := by
  constructor
  · rintro ⟨c, ⟨-, hcO⟩, rfl⟩
    exact hcO
  · intro h
    exact ⟨⟨g, hPC hg⟩, ⟨hg, h⟩, rfl⟩

theorem D1CentralizerInput3.le_centralizer {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} {z : G} (h : D1CentralizerInput3 p P M z) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp h.mem_centralizer x hx)

theorem D1ConstrainedReducedData3.map_sl_eq {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {E C : Subgroup (ReducedCentralizer p z)} [E.Normal]
    {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}
    (hdata : D1ConstrainedReducedData3 p P M z Pbar zbar)
    (hstr : ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    {F : Subgroup G} (hFP : F ≤ (P : Subgroup G)) (hFcard : Nat.card F = p ^ 3)
    (hFexp : ∀ x ∈ F, x ^ p = 1) (hFZ : (Subgroup.center F).map F.subtype = Subgroup.zpowers z)
    (eF : F ⧸ Subgroup.center F ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set G)).subgroupOf
      (Subgroup.normalizer (F : Set G))).map (centerQuotientAction F eF)) :
    (F.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore p)) = E := by
  have hp : p.Prime := Fact.out
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hFC : F ≤ Subgroup.centralizer ({z} : Set G) := hFP.trans hPC
  obtain ⟨φ, hφ⟩ := CFSG.AGLEmbedding.exists_mulEquiv_map_mk _ hp hO (P.isPGroup'.to_le hFP) hFC
  let zC : Subgroup.centralizer ({z} : Set G) :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hzbar := hdata.zbar_eq zC rfl
  have hFZbar := CFSG.AGLEmbedding.map_center_eq_zpowers_mk _ hFC φ hφ (zC := zC) hFZ
  have hSLbar := CFSG.AGLEmbedding.statedSL_le_map_mk _ hFC le_rfl φ hφ eF hSL
  have hFbarP : (F.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore p)) ≤ (Pbar : Subgroup (ReducedCentralizer p z)) := by
    rw [hdata.pbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hFP)
  refine eq_of_sl_subgroup hstr hdata.zbar_order hFbarP
    ((Nat.card_congr φ.toEquiv).symm.trans hFcard) ?_ (hzbar ▸ hFZbar) _ hSLbar
  rintro _ ⟨c, hc, rfl⟩
  rw [← map_pow]
  exact (congrArg _ (Subtype.ext (hFexp c hc))).trans (map_one _)

theorem D1ConstrainedReducedData3.sl_le_constrainedQ_and_normal {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {E C : Subgroup (ReducedCentralizer p z)} [E.Normal]
    {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}
    (hdata : D1ConstrainedReducedData3 p P M z Pbar zbar)
    (hstr : ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    {F : Subgroup G} (hFP : F ≤ (P : Subgroup G)) (hFcard : Nat.card F = p ^ 3)
    (hFexp : ∀ x ∈ F, x ^ p = 1) (hFZ : (Subgroup.center F).map F.subtype = Subgroup.zpowers z)
    (eF : F ⧸ Subgroup.center F ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤ ((Subgroup.centralizer ({z} : Set G)).subgroupOf
      (Subgroup.normalizer (F : Set G))).map (centerQuotientAction F eF)) :
    F ≤ constrainedQ p P z hPC ∧ (F.subgroupOf (P : Subgroup G)).Normal := by
  have hp : p.Prime := Fact.out
  have hEq := hdata.map_sl_eq hstr hPC hFP hFcard hFexp hFZ eF hSL
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hT : IsPGroup p ((P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))) :=
    P.isPGroup'.comap_subtype
  refine ⟨fun g hg => ?_, ⟨fun n hn x => ?_⟩⟩
  · exact (mem_constrainedQ_iff (hFP hg)).mpr
      (hstr.le_pCore (hEq ▸ ⟨⟨g, hPC (hFP hg)⟩, hg, rfl⟩))
  · have hnF : (n : G) ∈ F := hn
    have hyP : (x : G) * n * (x : G)⁻¹ ∈ (P : Subgroup G) :=
      P.mul_mem (P.mul_mem x.2 n.2) (P.inv_mem x.2)
    have hnE : QuotientGroup.mk' (primeComplementCore p) ⟨n, hPC n.2⟩ ∈ E :=
      hEq ▸ ⟨⟨n, hPC n.2⟩, hnF, rfl⟩
    have hyE := ‹E.Normal›.conj_mem _ hnE (QuotientGroup.mk' (primeComplementCore p) ⟨x, hPC x.2⟩)
    rw [← hEq] at hyE
    obtain ⟨f, hf, hfy⟩ := hyE
    have hfP : f ∈ (P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) :=
      hFP hf
    have hyP' : (⟨(x : G) * n * (x : G)⁻¹, hPC hyP⟩ : Subgroup.centralizer ({z} : Set G)) ∈
        (P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) := hyP
    have hmul : QuotientGroup.mk' (primeComplementCore p)
        (⟨(x : G) * n * (x : G)⁻¹, hPC hyP⟩ : Subgroup.centralizer ({z} : Set G)) =
        QuotientGroup.mk' (primeComplementCore p) ⟨x, hPC x.2⟩ *
          QuotientGroup.mk' (primeComplementCore p) ⟨n, hPC n.2⟩ *
          (QuotientGroup.mk' (primeComplementCore p) ⟨x, hPC x.2⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    have heq := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp _ hO hT hfP hyP' (hfy.trans hmul.symm)
    have hfy' : (f : G) = (x : G) * n * (x : G)⁻¹ := congrArg Subtype.val heq
    rw [Subgroup.mem_subgroupOf]
    have hxnx : ((x * n * x⁻¹ : (P : Subgroup G)) : G) = (x : G) * n * (x : G)⁻¹ := rfl
    rw [hxnx, ← hfy']
    exact hf

theorem D1ConstrainedReducedData3.relIndex_constrainedQ {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {E C : Subgroup (ReducedCentralizer p z)} [E.Normal]
    {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}
    (hdata : D1ConstrainedReducedData3 p P M z Pbar zbar)
    (hstr : ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) :
    (constrainedQ p P z hPC).relIndex (P : Subgroup G) = p := by
  set f : (P : Subgroup G) →* ReducedCentralizer p z :=
    (QuotientGroup.mk' (primeComplementCore p)).comp (Subgroup.inclusion hPC) with hf
  have hrange : f.range = (Pbar : Subgroup (ReducedCentralizer p z)) := by
    ext y
    rw [hdata.pbar, MonoidHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion hPC a, a.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hQ : (constrainedQ p P z hPC).subgroupOf (P : Subgroup G) =
      (CFSG.pCore p (ReducedCentralizer p z)).comap f := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact mem_constrainedQ_iff a.2
  rw [Subgroup.relIndex, hQ, Subgroup.index_comap, hrange]
  exact hstr.relIndex_eq

theorem D1ConstrainedReducedData3.map_inf_centralizer_eq {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {E C : Subgroup (ReducedCentralizer p z)} [E.Normal]
    {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}
    (hdata : D1ConstrainedReducedData3 p P M z Pbar zbar)
    (hstr : ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    {F : Subgroup G} (hFP : F ≤ (P : Subgroup G))
    (hFE : (F.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore p)) = E) :
    (((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G)).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore p)) = C := by
  have hp : p.Prime := Fact.out
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hT : IsPGroup p ((P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))) :=
    P.isPGroup'.comap_subtype
  ext y
  constructor
  · rintro ⟨c, ⟨hcP, hcF⟩, rfl⟩
    rw [← hstr.centralizer_eq, Subgroup.mem_centralizer_iff]
    intro y' hy'
    rw [← hFE] at hy'
    obtain ⟨d, hd, rfl⟩ := hy'
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp hcF d hd))
  · intro hy
    have hyP : y ∈ (Pbar : Subgroup (ReducedCentralizer p z)) := hstr.le_sylow hy
    rw [hdata.pbar] at hyP
    obtain ⟨c, hcP, rfl⟩ := hyP
    refine ⟨c, ⟨hcP, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩, rfl⟩
    have hgP : g ∈ (P : Subgroup G) := hFP hg
    have hgC : g ∈ Subgroup.centralizer ({z} : Set G) := hPC hgP
    have hgE : QuotientGroup.mk' (primeComplementCore p) ⟨g, hgC⟩ ∈ E :=
      hFE ▸ ⟨⟨g, hgC⟩, hg, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp (hstr.centralizer_eq ▸ hy) _ hgE
    exact congrArg Subtype.val (CFSG.AGLEmbedding.commute_of_mk_commute hp _ hO hT
      (show (⟨g, hgC⟩ : Subgroup.centralizer ({z} : Set G)) ∈ _ from hgP) hcP hcomm)

theorem D1ConstrainedReducedData3.constrainedQ_eq_sup {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {E C : Subgroup (ReducedCentralizer p z)} [E.Normal]
    {e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)}
    (hdata : D1ConstrainedReducedData3 p P M z Pbar zbar)
    (hstr : ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e)
    (hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    {F : Subgroup G} (hFP : F ≤ (P : Subgroup G))
    (hFZ : (Subgroup.center F).map F.subtype = Subgroup.zpowers z)
    (hFE : (F.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore p)) = E) :
    constrainedQ p P z hPC = F ⊔ ((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G)) ∧
      IsCyclic ((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) ∧
      (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G), y ^ p = 1 →
        y ∈ Subgroup.zpowers z) ∧
      F ⊓ ((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G)) = Subgroup.zpowers z := by
  have hp : p.Prime := Fact.out
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hT : IsPGroup p ((P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))) :=
    P.isPGroup'.comap_subtype
  have hCGmap := hdata.map_inf_centralizer_eq hstr hPC hFP hFE
  have hzF : Subgroup.zpowers z ≤ F := hFZ ▸ Subgroup.map_subtype_le _
  have hCP : (P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G) ≤ Subgroup.centralizer
      ({z} : Set G) := fun g hg => hPC hg.1
  refine ⟨le_antisymm (fun q hq => ?_) (sup_le (fun g hg => ?_) (fun g hg => ?_)), ?_, ?_, ?_⟩
  ·
    obtain ⟨c, ⟨hcP, hcO⟩, rfl⟩ := hq
    have hcQ : QuotientGroup.mk' (primeComplementCore p) c ∈
        CFSG.pCore p (ReducedCentralizer p z) := hcO
    have hcP' : c ∈ (P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) := hcP
    obtain ⟨e', he', c', hc', hmul⟩ := exists_mul_eq_of_mem_sup_normal (hstr.sup_eq ▸ hcQ)
    rw [← hFE] at he'
    rw [← hCGmap] at hc'
    obtain ⟨f₀, hf₀, rfl⟩ := he'
    obtain ⟨c₀, hc₀, rfl⟩ := hc'
    have heq := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp _ hO hT
      (show f₀ * c₀ ∈ (P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) from
        (P : Subgroup G).mul_mem (hFP hf₀) hc₀.1) hcP' (by rw [map_mul]; exact hmul)
    have hqe : ((c : Subgroup.centralizer ({z} : Set G)) : G) = (f₀ : G) * (c₀ : G) :=
      congrArg Subtype.val heq.symm
    show ((c : Subgroup.centralizer ({z} : Set G)) : G) ∈ _
    rw [hqe]
    exact Subgroup.mul_mem_sup hf₀ hc₀
  · exact (mem_constrainedQ_iff (hFP hg)).mpr (hstr.le_pCore (hFE ▸ ⟨⟨g, hPC (hFP hg)⟩, hg, rfl⟩))
  · refine (mem_constrainedQ_iff hg.1).mpr ?_
    have : QuotientGroup.mk' (primeComplementCore p) ⟨g, hPC hg.1⟩ ∈ C :=
      hCGmap ▸ ⟨⟨g, hPC hg.1⟩, hg, rfl⟩
    exact hstr.sup_eq ▸ (le_sup_right : C ≤ E ⊔ C) this
  · obtain ⟨φ, -⟩ := CFSG.AGLEmbedding.exists_mulEquiv_map_mk _ hp hO
      (P.isPGroup'.to_le inf_le_left) hCP
    have : IsCyclic (((((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G)).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)))) :=
      hCGmap ▸ hstr.isCyclic
    exact isCyclic_of_surjective φ.symm.toMonoidHom φ.symm.surjective
  · intro y hy hyp
    let yC : Subgroup.centralizer ({z} : Set G) := ⟨y, hCP hy⟩
    have hyC : QuotientGroup.mk' (primeComplementCore p) yC ∈ C := by
      rw [← hCGmap]
      exact ⟨yC, hy, rfl⟩
    have hpow : (QuotientGroup.mk' (primeComplementCore p) yC) ^ p = 1 := by
      rw [← map_pow]
      exact (congrArg _ (Subtype.ext hyp)).trans (map_one _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hstr.omega_le _ hyC hpow)
    let zC : Subgroup.centralizer ({z} : Set G) :=
      ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hzP : z ∈ (P : Subgroup G) := hFP (hzF (Subgroup.mem_zpowers z))
    have hzCT : zC ∈ (P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) := hzP
    have heq := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp _ hO hT
      (Subgroup.zpow_mem _ hzCT k) (show yC ∈
        (P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) from hy.1)
      (by rw [map_zpow, hdata.zbar_eq zC rfl]; exact hk)
    exact ⟨k, congrArg Subtype.val heq⟩
  · apply le_antisymm
    · rintro y ⟨hyF, -, hyc⟩
      have h1 : y ∈ F ⊓ Subgroup.centralizer (F : Set G) := ⟨hyF, hyc⟩
      rwa [inf_centralizer_eq_of_center_map hFZ] at h1
    · intro y hy
      refine ⟨hzF hy, hFP (hzF hy), ?_⟩
      have hy' : y ∈ (Subgroup.center F).map F.subtype := by rw [hFZ]; exact hy
      obtain ⟨c, hc, rfl⟩ := hy'
      exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)

end Lift

end CFSG.LocalAnalysis.RankThreeTheoremC
