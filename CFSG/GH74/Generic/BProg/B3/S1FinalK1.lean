module

public import CFSG.GH74.Generic.BProg.B3.S1Split
public import CFSG.GH74.Generic.BProg.B3.S1FinalSl2

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalK1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS1
open CFSG.GH74.Generic.BProg.B3.S1SplitAux
open scoped MatrixGroups commutatorElement

section Subtype

variable {X : Type} [Group X] {F : Type} [Field F] [Finite F] {Y : Subgroup X} {z u : X}
  {J₁ J₂ : Subgroup X}

theorem SplitAt.of_subtype (h : SplitAt F Y z u J₁ J₂) (hz : z ∈ Y) (hu : u ∈ Y) :
    SplitAt F (⊤ : Subgroup ↥Y) ⟨z, hz⟩ ⟨u, hu⟩ (J₁.subgroupOf Y) (J₂.subgroupOf Y) := by
  have hJ₁Y : J₁ ≤ Y := fun j hj => (h.le₁ hj).2
  have hJ₂Y : J₂ ≤ Y := fun j hj => (h.le₂ hj).2
  have hcen : ∀ g : ↥Y, g * (⟨u, hu⟩ : ↥Y) = ⟨u, hu⟩ * g ↔ (g : X) * u = u * (g : X) :=
    fun g => ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact h.ord
  · intro g hg
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 ((hcen g).2
      (Subgroup.mem_centralizer_singleton_iff.1 (h.le₁ (Subgroup.mem_subgroupOf.1 hg)).1)),
      trivial⟩
  · intro g hg
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 ((hcen g).2
      (Subgroup.mem_centralizer_singleton_iff.1 (h.le₂ (Subgroup.mem_subgroupOf.1 hg)).1)),
      trivial⟩
  · intro a _ b _ hau hbu
    have h1 := h.comm (a : X) a.2 (b : X) b.2 ((hcen a).1 hau) ((hcen b).1 hbu)
    rw [← Subgroup.subgroupOf_sup hJ₁Y hJ₂Y]
    exact h1
  · intro a _ hau j hj
    exact h.norm₁ (a : X) a.2 ((hcen a).1 hau) (j : X) (Subgroup.mem_subgroupOf.1 hj)
  · intro a _ hau j hj
    exact h.norm₂ (a : X) a.2 ((hcen a).1 hau) (j : X) (Subgroup.mem_subgroupOf.1 hj)
  · intro a ha b hb
    exact Subtype.ext (h.commute (a : X) (Subgroup.mem_subgroupOf.1 ha) (b : X)
      (Subgroup.mem_subgroupOf.1 hb))
  · rw [Subgroup.disjoint_def]
    intro g hg1 hg2
    have := Subgroup.disjoint_def.1 h.disj (Subgroup.mem_subgroupOf.1 hg1)
      (Subgroup.mem_subgroupOf.1 hg2)
    exact Subtype.ext this
  · exact Subgroup.mem_subgroupOf.2 h.u_mem
  · exact Subgroup.mem_subgroupOf.2 h.zu_mem
  · obtain ⟨e⟩ := h.equiv₁
    exact ⟨(Subgroup.subgroupOfEquivOfLe hJ₁Y).trans e⟩
  · obtain ⟨e⟩ := h.equiv₂
    exact ⟨(Subgroup.subgroupOfEquivOfLe hJ₂Y).trans e⟩
  · intro d _ hdd hdj
    have hdd' : (d : X) * d = 1 := congrArg Subtype.val hdd
    have hdj' : ∀ j ∈ J₁, (d : X) * j = j * d := fun j hj =>
      congrArg Subtype.val (hdj ⟨j, hJ₁Y hj⟩ (Subgroup.mem_subgroupOf.2 hj))
    rcases h.invol (d : X) d.2 hdd' hdj' with h1 | h1 | h1 | h1
    · left; exact Subtype.ext h1
    · right; left; exact Subtype.ext h1
    · right; right; left; exact Subtype.ext h1
    · right; right; right; exact Subtype.ext h1
  · intro hF a _ hau
    have h1 := h.sq_mem hF (a : X) a.2 ((hcen a).1 hau)
    rw [← Subgroup.subgroupOf_sup hJ₁Y hJ₂Y]
    exact h1

end Subtype

section Main

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}
  {J₁ J₂ : Subgroup G}

theorem exists_splitAt_bar (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K)) (hax : a ≠ x)
    (hS : S1SplitMod K A x a J₁ J₂) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Odd (Nat.card F') ∧ 4 ≤ Nat.card F' ∧
      SplitAt F' (imgBar x K) (xbar x) (bar x a) (imgBar x J₁) (imgBar x J₂) ∧
      (∀ L : Subgroup G, IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) L → L = J₁ ∨ L = J₂) ∧
      (∀ L : Subgroup G, IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) L →
        imgBar x L = imgBar x J₂ → L = J₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, _, F', _, _, z₀, ⟨eP⟩, hodd, hbig, hP⟩ := B1.PilotS1.exists_grpS1_of_big h1
  have hx2 : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  obtain ⟨hxK, -, -, hY, -, he8⟩ := B1.PilotS1.shape1_data hc.hyp.gen4 hx2 hK eP hP
    (B1.PilotS1.QShape1Big.qShape1 h1)
  obtain ⟨hAK, hAel, hA8⟩ := B1.PilotS1.source_le hxK hc.src
  obtain ⟨hxA, -⟩ := B1.PilotS1.exists_y_of_e8 hx2 hK he8 hAK hAel hA8
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hAsq : ∀ c ∈ A, c * c = 1 := fun c hc' => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) c hc'
  have hAcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := fun c hc' d hd =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨c, hc'⟩ ⟨d, hd⟩)
  have haA : a ∈ A := hc.a_mem
  have haK : a ∈ K := hAK haA
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have haC : a ∈ centralizer ({x} : Set G) := hKC haK
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨hub, hub1, hub2⟩ := bar_facts hKC haK ha2
  have hubx : bar x a ≠ xbar x := by
    intro h
    apply hax
    refine B1.PilotS1.eq_of_proj_eq haC hxC (hAcomm a haA x hxA) (hAsq a haA) (hAsq x hxA) ?_
    rw [← bar_of_mem haC]; exact h
  obtain ⟨Jb₁, Jb₂, hSp⟩ := hY.split (bar x a) hub hub2 hubx
  set Hg : Subgroup G := K ⊓ centralizer ({a} : Set G) with hHg
  set φ : ↥Hg →* CentralizerBar x := S1Split.phiHom x a hKC with hφ
  have hker : Odd (Nat.card φ.ker) := S1Split.odd_card_ker_phiHom x a hKC
  have hrange : φ.range = centralizer ({bar x a} : Set (CentralizerBar x)) ⊓ imgBar x K :=
    S1Split.range_phiHom x hKC haK ha2
  have h₁ : IsPCompIn 2 φ.range Jb₁ := by rw [hrange]; exact hSp.isPCompIn₁ hodd hbig
  have h₂ : IsPCompIn 2 φ.range Jb₂ := by rw [hrange]; exact hSp.isPCompIn₂ hodd hbig
  have hall : ∀ M : Subgroup (CentralizerBar x), IsPCompIn 2 φ.range M → M = Jb₁ ∨ M = Jb₂ := by
    intro M hM
    rw [hrange] at hM
    exact eq_or_eq_of_isPCompIn hodd hbig hSp hM
  have hJ₁le : J₁ ≤ Hg := hS.comp₁.1
  have hJ₂le : J₂ ≤ Hg := hS.comp₂.1
  have himg : ∀ L : Subgroup G, L ≤ Hg → imgBar x L = (L.subgroupOf Hg).map φ := by
    intro L hL
    ext c
    constructor
    · intro hcL
      obtain ⟨g, hg, rfl⟩ := mem_imgBar.1 hcL
      exact ⟨⟨(g : G), hL hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact mem_imgBar.2 ⟨⟨(y : G), hKC y.2.1⟩, Subgroup.mem_subgroupOf.1 hy, rfl⟩
  have huHg : a ∈ Hg := ⟨haK, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hφu : φ ⟨a, huHg⟩ = bar x a := (bar_of_mem haC).symm
  have hJ₁img := S1SplitAux.isPCompIn_map hker hS.comp₁
  have hJ₂img := S1SplitAux.isPCompIn_map hker hS.comp₂
  have hdist : (J₁.subgroupOf Hg).map φ ≠ (J₂.subgroupOf Hg).map φ := fun h =>
    hS.ne (S1SplitAux.eq_of_map_eq hker hS.comp₁ hS.comp₂ h)
  have haimg : bar x a ∈ (J₁.subgroupOf Hg).map φ :=
    ⟨⟨a, huHg⟩, Subgroup.mem_subgroupOf.2 hS.u_mem, hφu⟩
  have hI₁ : (J₁.subgroupOf Hg).map φ = Jb₁ := by
    rcases hall _ hJ₁img with h | h
    · exact h
    · exfalso
      have hmem2 : bar x a ∈ Jb₂ := h ▸ haimg
      exact hub1 (Subgroup.disjoint_def.1 hSp.disj hSp.u_mem hmem2)
  have hI₂ : (J₂.subgroupOf Hg).map φ = Jb₂ := by
    rcases hall _ hJ₂img with h | h
    · exfalso
      exact hdist (hI₁.trans h.symm)
    · exact h
  refine ⟨F', inferInstance, inferInstance, hodd, hbig, ?_, ?_, ?_⟩
  · rw [himg J₁ hJ₁le, himg J₂ hJ₂le, hI₁, hI₂]
    exact hSp
  · intro L hL
    rcases hall _ (S1SplitAux.isPCompIn_map hker hL) with h | h
    · left
      exact S1SplitAux.eq_of_map_eq hker hL hS.comp₁ (h.trans hI₁.symm)
    · right
      exact S1SplitAux.eq_of_map_eq hker hL hS.comp₂ (h.trans hI₂.symm)
  · intro L hL himgeq
    rw [himg L hL.1, himg J₂ hJ₂le] at himgeq
    exact S1SplitAux.eq_of_map_eq hker hL hS.comp₂ himgeq

end Main

section Proj

variable {G : Type} [Group G] {x : G}

@[expose] noncomputable def restrBar {J : Subgroup G} (hJC : J ≤ centralizer ({x} : Set G)) :
    ↥J →* ↥(imgBar x J) :=
  ((proj x).comp (Subgroup.inclusion hJC)).codRestrict (imgBar x J)
    (fun j => ⟨⟨(j : G), hJC j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩)

theorem restrBar_surjective {J : Subgroup G} (hJC : J ≤ centralizer ({x} : Set G)) :
    Function.Surjective (restrBar hJC) := by
  rintro ⟨_, ⟨c, hc, rfl⟩⟩
  exact ⟨⟨(c : G), Subgroup.mem_subgroupOf.1 hc⟩, Subtype.ext rfl⟩

theorem proj_eq_one_of_odd_normal {J : Subgroup G} (hJC : J ≤ centralizer ({x} : Set G))
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (hF : 5 ≤ Nat.card F)
    (e : ↥(imgBar x J) ≃* SL(2, F)) (N : Subgroup ↥J) [N.Normal] (hN : Odd (Nat.card N)) :
    ∀ n ∈ N, proj x ⟨(n : G), hJC n.2⟩ = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hodd hF
  set θ : ↥J →* SL(2, F) := e.toMonoidHom.comp (restrBar hJC) with hθ
  have hθs : Function.Surjective θ := e.surjective.comp (restrBar_surjective hJC)
  intro n hn
  have h1 := S1FinalSl2.normal_odd_le_ker hodd hF θ hθs N hN hn
  have h2 : θ n = 1 := h1
  have h3 : restrBar hJC n = 1 := e.injective (by rw [map_one]; exact h2)
  have h4 := congrArg Subtype.val h3
  exact h4

theorem mem_pPrimeCoreOf_of_proj_eq_one [Finite G] {J : Subgroup G}
    (hJC : J ≤ centralizer ({x} : Set G)) {g : G} (hgJ : g ∈ J)
    (hg : proj x ⟨g, hJC hgJ⟩ = 1) : g ∈ pPrimeCoreOf 2 J :=
  ⟨⟨g, hgJ⟩, S1Split.ker_fK_le x hJC (MonoidHom.mem_ker.2 hg), rfl⟩

end Proj

end S1FinalK1

end CFSG.GH74.Generic.BProg.B3
