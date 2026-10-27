module

public import CFSG.CGT.PushingUpLit.C2L.Gomi42
public import CFSG.CGT.PushingUpLit.C2L.Gomi41
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open CFSG.RankThree.PartOne (omegaOneCenterIn)
open scoped commutatorElement

variable {G : Type} [Group G]

structure Gomi46Facts (G : Type) [Group G] : Prop where
  l45_three : ∀ P D₁ D₂ Q₁ Q₂ : Subgroup G, IsSylowOf 2 P ⊤ → GomiE P D₁ D₂ →
    IsOtherSylow P D₁ Q₁ → IsOtherSylow P D₂ Q₂ →
    (omegaOneCenterIn Q₁ ≤ D₂ ↔ omegaOneCenterIn Q₂ ≤ D₁)
  l46_two : ∀ P D₁ D₂ Q₁ : Subgroup G, IsSylowOf 2 P ⊤ → GomiE' P D₁ D₂ →
    IsOtherSylow P D₁ Q₁ →
    D₁ = omegaOneCenterIn Q₁ ⊔ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))
  l46_four : ∀ P D₁ D₂ A : Subgroup G, IsSylowOf 2 P ⊤ → GomiE' P D₁ D₂ →
    A ≤ P ⊓ Subgroup.normalizer (D₁ : Set G) → CFSG.Open.IsElemAbelian 2 A → A ≤ D₁ ∨ A ≤ D₂

namespace Gomi47

omit [Group G] in
theorem mem_map_conj_inv_iff' [Group G] {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

theorem mem_map_conj_iff' {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  simpa using (mem_map_conj_inv_iff' (H := H) (g := g⁻¹) (y := y))

variable [Finite G]

theorem isSylowOf_top_of_le {S N R : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hSN : S ≤ N)
    (hR : IsSylowOf 2 R N) : IsSylowOf 2 R ⊤ := by
  obtain ⟨n, -, hn⟩ := exists_eq_map_conj_of_isSylowOf (hS.of_le hSN le_top) hR
  rw [hn]
  exact isSylowOf_top_map_conj hS n

theorem false_of_invariant_assignment
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (f : Subgroup G → Subgroup G) {P : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hfH : GomiH (f P)) (hfP : f P ≤ P) (hPN : P ≤ Subgroup.normalizer (f P : Set G))
    (hconj : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ∀ g : G,
      f (S.map (MulAut.conj g).toMonoidHom) = (f S).map (MulAut.conj g).toMonoidHom)
    (hcon : ∀ A B : Subgroup G, IsSylowOf 2 A ⊤ → IsSylowOf 2 B ⊤ → A ⊓ B ≠ ⊥ → f A = f B) :
    False := by
  have hH₁ne : f P ≠ ⊥ := hfH.ne_bot
  have hH₁2 : IsPGroup 2 (f P) := hfH.isPGroup
  have hH₁N : f P ≤ Subgroup.normalizer (f P : Set G) := Subgroup.le_normalizer
  have hPN' : IsSylowOf 2 P (Subgroup.normalizer (f P : Set G)) := hP.of_le hPN le_top
  have hNsyl : ∀ Q : Subgroup G, IsSylowOf 2 Q (Subgroup.normalizer (f P : Set G)) →
      IsSylowOf 2 Q ⊤ := fun Q hQ => isSylowOf_top_of_le hP hPN hQ
  have hNf : ∀ Q : Subgroup G, IsSylowOf 2 Q (Subgroup.normalizer (f P : Set G)) → f Q = f P := by
    intro Q hQ
    have hH₁Q : f P ≤ Q := le_of_isSylowOf_of_normal hQ hH₁N le_rfl hH₁2
    refine (hcon P Q hP (hNsyl Q hQ) fun h => hH₁ne ?_).symm
    have := le_inf hfP hH₁Q
    rw [h] at this
    exact le_bot_iff.1 this
  have hSE : CFSG.Open.fusionStronglyEmbedded (Subgroup.normalizer (f P : Set G)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro htop
      exact hH₁ne (hO2 (f P) (Subgroup.normalizer_eq_top_iff.1 htop) hH₁2)
    · have hP0 : P ≠ ⊥ := fun h => hH₁ne (le_bot_iff.1 (h ▸ hfP))
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP.isPGroup
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hP0 ((Subgroup.eq_bot_iff_card P).2 (by simpa using hk))
      exact even_iff_two_dvd.2 ((hk ▸ dvd_pow_self 2 hk0).trans (Subgroup.card_dvd_of_le hPN))
    · intro g hg
      by_contra hodd
      rw [Nat.not_odd_iff_even] at hodd
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
      have htN : (t : G) ∈ Subgroup.normalizer (f P : Set G) := t.2.1
      have htNg : (t : G) ∈
          (Subgroup.normalizer (f P : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := t.2.2
      have hord : orderOf (t : G) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact ht
      have ht1 : (t : G) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hord
        omega
      have hvN : g * (t : G) * g⁻¹ ∈ Subgroup.normalizer (f P : Set G) :=
        mem_map_conj_inv_iff'.1 htNg
      have hvord : orderOf (g * (t : G) * g⁻¹) = 2 := by
        rw [← hord]
        simpa [mul_assoc] using orderOf_injective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective (t : G)
      have hzp : ∀ s : G, orderOf s = 2 → IsPGroup 2 (Subgroup.zpowers s) := fun s hs => by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, hs, pow_one]
      obtain ⟨Q, hQ, hQt⟩ := exists_isSylowOf_ge ((Subgroup.zpowers_le).2 htN) (hzp _ hord)
      obtain ⟨R, hR, hRv⟩ := exists_isSylowOf_ge ((Subgroup.zpowers_le).2 hvN) (hzp _ hvord)
      have htQ : (t : G) ∈ Q := hQt (Subgroup.mem_zpowers _)
      have hvR : g * (t : G) * g⁻¹ ∈ R := hRv (Subgroup.mem_zpowers _)
      have hRg : IsSylowOf 2 (R.map (MulAut.conj g⁻¹).toMonoidHom) ⊤ :=
        isSylowOf_top_map_conj (hNsyl R hR) g⁻¹
      have htRg : (t : G) ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := mem_map_conj_inv_iff'.2 hvR
      have hne : Q ⊓ R.map (MulAut.conj g⁻¹).toMonoidHom ≠ ⊥ := by
        intro h
        have : (t : G) ∈ Q ⊓ R.map (MulAut.conj g⁻¹).toMonoidHom := ⟨htQ, htRg⟩
        rw [h, Subgroup.mem_bot] at this
        exact ht1 this
      have heq := hcon Q _ (hNsyl Q hQ) hRg hne
      rw [hNf Q hQ, hconj R (hNsyl R hR) g⁻¹, hNf R hR] at heq
      have hginv : g⁻¹ ∈ Subgroup.normalizer (f P : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.2 heq.symm
      exact hg (by simpa using Subgroup.inv_mem _ hginv)
  obtain ⟨R, hR, hRP, hH₁R⟩ := hfH.exists_sylow_ne P
  have hTI := StrongTI.sylow_inf_eq_bot_of_stronglyEmbedded hSE hO hO2 hP hR (Ne.symm hRP)
  have := le_inf hfP hH₁R
  rw [hTI] at this
  exact hH₁ne (le_bot_iff.1 this)

@[expose] def Dtop (S : Subgroup G) : Subgroup G := sInf {D : Subgroup G | GomiD S D}

omit [Finite G] in
theorem Dtop_le {S D : Subgroup G} (h : GomiD S D) : Dtop S ≤ D := sInf_le h

omit [Finite G] in
theorem le_Dtop {S E : Subgroup G} (h : ∀ D : Subgroup G, GomiD S D → E ≤ D) : E ≤ Dtop S :=
  le_sInf h

theorem gomiD_map_conj_iff {S D : Subgroup G} (g : G) :
    GomiD (S.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom) ↔ GomiD S D := by
  refine ⟨fun h => ?_, fun h => h.map_conj g⟩
  have := h.map_conj g⁻¹
  rwa [map_conj_inv_map_conj, map_conj_inv_map_conj] at this

theorem Dtop_map_conj (S : Subgroup G) (g : G) :
    Dtop (S.map (MulAut.conj g).toMonoidHom) = (Dtop S).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [mem_map_conj_iff']
  simp only [Dtop, Subgroup.mem_sInf, Set.mem_ofPred_eq]
  constructor
  · intro h D hD
    have h1 := h (D.map (MulAut.conj g).toMonoidHom) ((gomiD_map_conj_iff g).2 hD)
    exact mem_map_conj_iff'.1 h1
  · intro h D hD
    have hD' : GomiD S (D.map (MulAut.conj g⁻¹).toMonoidHom) := by
      have := hD.map_conj g⁻¹
      rwa [map_conj_inv_map_conj] at this
    have h2 := mem_map_conj_inv_iff'.1 (h _ hD')
    simpa [mul_assoc] using h2

@[expose] def DtopP1 (S : Subgroup G) : Prop :=
  GomiH (Dtop S) ∧ S ≤ Subgroup.normalizer (Dtop S : Set G)

@[expose] def DtopP2 (S : Subgroup G) : Prop := ∀ H : Subgroup G, GomiH0In S H → Dtop S ≤ H

theorem DtopP1.map_conj {S : Subgroup G} (h : DtopP1 S) (g : G) :
    DtopP1 (S.map (MulAut.conj g).toMonoidHom) := by
  unfold DtopP1
  rw [Dtop_map_conj]
  refine ⟨h.1.map_conj g, ?_⟩
  have hN : (Subgroup.normalizer (Dtop S : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer (((Dtop S).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq (Dtop S) (MulAut.conj g)
  rw [← hN]
  exact Subgroup.map_mono h.2

theorem DtopP2.map_conj {S : Subgroup G} (h : DtopP2 S) (g : G) :
    DtopP2 (S.map (MulAut.conj g).toMonoidHom) := by
  intro H hH
  rw [Dtop_map_conj]
  have h1 : GomiH0In S (H.map (MulAut.conj g⁻¹).toMonoidHom) := by
    refine ⟨hH.1.map_conj g⁻¹, ?_⟩
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hH.2
    rwa [map_conj_inv_map_conj] at this
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (h _ h1)
  rwa [map_conj_map_conj_inv] at h2

theorem dtopP12_of_sylow {P S : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hS : IsSylowOf 2 S ⊤)
    (h1 : DtopP1 P) (h2 : DtopP2 P) : DtopP1 S ∧ DtopP2 S := by
  obtain ⟨g, -, hg⟩ := exists_eq_map_conj_of_isSylowOf hP hS
  rw [hg]
  exact ⟨h1.map_conj g, h2.map_conj g⟩

theorem Dtop_eq_of_link (hc : CFSG.Assembly.IsCharTwoType G)
    (hcl : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S) {A B D : Subgroup G}
    (hA1 : DtopP1 A) (hA2 : DtopP2 A) (hlink : TameLink D A B) : Dtop A = Dtop B := by
  have hK : GomiH0 (A ⊓ B) := hlink.2.2.2.2.2
  have hDB : Dtop A ≤ B := (hA2 _ ⟨hK, inf_le_left⟩).trans inf_le_right
  have hBN : B ≤ Subgroup.normalizer (Dtop A : Set G) :=
    GomiH.le_normalizer_of_classLETwo hc hA1.1 (hcl B hlink.2.1) hDB
  have hAN' : IsSylowOf 2 A (Subgroup.normalizer (Dtop A : Set G)) :=
    hlink.1.of_le hA1.2 le_top
  have hBN' : IsSylowOf 2 B (Subgroup.normalizer (Dtop A : Set G)) :=
    hlink.2.1.of_le hBN le_top
  obtain ⟨n, hn, hBn⟩ := exists_eq_map_conj_of_isSylowOf hAN' hBN'
  rw [hBn, Dtop_map_conj]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq.1 hn).symm

theorem Dtop_eq_of_inf_ne_bot (hc : CFSG.Assembly.IsCharTwoType G)
    (hcl : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S)
    (hall : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → DtopP1 S ∧ DtopP2 S) {A B : Subgroup G}
    (hA : IsSylowOf 2 A ⊤) (hB : IsSylowOf 2 B ⊤) (h : A ⊓ B ≠ ⊥) : Dtop A = Dtop B := by
  have hchain := tameChain_of_inf_ne_bot hA hB h
  suffices H : ∀ S : Subgroup G, Relation.ReflTransGen (TameLink (A ⊓ B)) A S →
      Dtop A = Dtop S from H B hchain
  intro S hS
  induction hS with
  | refl => rfl
  | @tail S S' _ hlink ih =>
    exact ih.trans (Dtop_eq_of_link hc hcl (hall S hlink.1).1 (hall S hlink.1).2 hlink)

theorem eq_or_eq_of_normalized
    (hc : CFSG.Assembly.IsCharTwoType G) {P H D : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hcl : ClassLETwo P) (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → z * z = 1)
    (hH : GomiH0 H) (hHP : H ≤ P) (hHD : H ≤ D) (hDP : D ≤ P)
    (hD : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) → g ∈ Subgroup.normalizer (P : Set G) →
      g ∈ Subgroup.normalizer (D : Set G)) : D = H ∨ D = P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hDH, hDP'⟩ := hcon
  have hHD' : H < D := lt_of_le_of_ne hHD (Ne.symm hDH)
  have hDPlt : D < P := lt_of_le_of_ne hDP hDP'
  have hHltP : H < P := lt_trans hHD' hDPlt
  have hHg : GomiH H := hH.1
  have hPN : P ≤ Subgroup.normalizer (H : Set G) := hHg.le_normalizer_of_classLETwo hc hcl hHP
  have hcenter : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → z ∈ H := fun z hz hzc =>
    hHg.center_le hc hHP ⟨hz, Subgroup.mem_centralizer_iff.2 hzc⟩
  have hcommP : ∀ x ∈ P, ∀ w ∈ P, ⁅x, w⁆ ∈ P := fun x hx w hw => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hx hw) (P.inv_mem hx)) (P.inv_mem hw)
  have hcentral : ∀ x ∈ P, ∀ w ∈ P, ∀ y ∈ P, y * ⁅x, w⁆ = ⁅x, w⁆ * y := fun x hx w hw y hy =>
    (commutatorElement_eq_one_iff_mul_comm.1 (hcl x hx w hw y hy)).symm
  have hcomm : ∀ x ∈ P, ∀ w ∈ P, ⁅x, w⁆ ∈ H := fun x hx w hw =>
    hcenter _ (hcommP x hx w hw) (hcentral x hx w hw)
  have hsq : ∀ x ∈ P, x ^ 2 ∈ H := by
    intro x hx
    rw [pow_two]
    refine hcenter _ (P.mul_mem hx hx) fun w hw => ?_
    obtain ⟨c, hc'⟩ : ∃ c : G, c = ⁅x, w⁆ := ⟨_, rfl⟩
    have hcc : c * c = 1 := hc' ▸ hZ _ (hcommP x hx w hw) (hcentral x hx w hw)
    have hxc : x * c = c * x := hc' ▸ hcentral x hx w hw x hx
    have hxw : x * w = c * w * x := by
      rw [hc', commutatorElement_def]
      group
    calc w * (x * x) = (w * x) * x := (mul_assoc _ _ _).symm
      _ = (c * c * w * x) * x := by rw [hcc, one_mul]
      _ = c * (c * w * x) * x := by group
      _ = c * (x * w) * x := by rw [hxw]
      _ = (c * x) * w * x := by group
      _ = (x * c) * w * x := by rw [hxc]
      _ = x * (c * w * x) := by group
      _ = x * (x * w) := by rw [← hxw]
      _ = (x * x) * w := by group
  have hHq : ∀ x ∈ P, ∀ y ∈ P, x ^ 2 ∈ H ∧ ⁅x, y⁆ ∈ H :=
    fun x hx y hy => ⟨hsq x hx, hcomm x hx y hy⟩
  set N : Subgroup G := Subgroup.normalizer (H : Set G) with hN
  have hHN : H ≤ N := Subgroup.le_normalizer
  have hDN : D ≤ N := hDP.trans hPN
  have hsyl : IsSylowOf 2 (P.subgroupOf N) ⊤ := by
    rw [isSylowOf_iff]
    obtain ⟨-, hPp, hPi⟩ := isSylowOf_iff.1 hP
    rw [Subgroup.relIndex_top_right] at hPi
    refine ⟨le_top, hPp.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h
    exact hPi (h.trans (Subgroup.relIndex_dvd_index_of_le hPN))
  have hlt' : H.subgroupOf N < P.subgroupOf N := by
    refine lt_of_le_of_ne (fun x hx => hHP hx) fun h => ?_
    obtain ⟨t, htP, htH⟩ := IsConcreteLE.exists_of_lt hHltP
    have ht : (⟨t, hPN htP⟩ : N) ∈ P.subgroupOf N := htP
    rw [← h] at ht
    exact htH ht
  have hTQ' : ∀ x ∈ P.subgroupOf N, ∀ y ∈ P.subgroupOf N,
      x ^ 2 ∈ H.subgroupOf N ∧ ⁅x, y⁆ ∈ H.subgroupOf N := by
    intro x hx y hy
    have h := hHq (x : G) hx (y : G) hy
    refine ⟨Subgroup.mem_subgroupOf.2 ?_, Subgroup.mem_subgroupOf.2 ?_⟩
    · simpa using h.1
    · simpa [commutatorElement_def] using h.2
  rcases Gomi41.bender_quotient (Z := ↥N) (T := P.subgroupOf N) (Q := H.subgroupOf N) hsyl
      (fun x hx => hHP hx) hlt' hTQ' hH.2 with hcard | hirr
  ·
    have e1 : Nat.card ↥(P.subgroupOf N) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
    have e2 : Nat.card ↥(H.subgroupOf N) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
    rw [e1, e2] at hcard
    have hHpos : 0 < Nat.card H := Nat.card_pos
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHD
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hDP
    have h1 : Nat.card H * (m * k) = Nat.card H * 2 := by
      calc Nat.card H * (m * k) = Nat.card D * k := by rw [hm]; ring
        _ = Nat.card P := hk.symm
        _ = 2 * Nat.card H := hcard
        _ = Nat.card H * 2 := by ring
    have hmk : m * k = 2 := Nat.eq_of_mul_eq_mul_left hHpos h1
    rcases (Nat.dvd_prime Nat.prime_two).1 (⟨k, hmk.symm⟩ : m ∣ 2) with hm1 | hm2
    · subst hm1
      exact hDH (Subgroup.eq_of_le_of_card_ge hHD (by omega)).symm
    · subst hm2
      have hk1 : k = 1 := by omega
      subst hk1
      exact hDP' (Subgroup.eq_of_le_of_card_ge hDP (by omega))
  ·
    have hNT : Subgroup.normalizer ((P.subgroupOf N : Subgroup ↥N) : Set ↥N) ≤
        Subgroup.normalizer ((D.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      intro z hz
      have hzP : (z : G) ∈ Subgroup.normalizer (P : Set G) := by
        apply Gomi41.mem_normalizer_of_forall_conj_mem
        intro y hy
        exact (Subgroup.mem_normalizer_iff.1 hz ⟨y, hPN hy⟩).1 hy
      have hzD : (z : G) ∈ Subgroup.normalizer (D : Set G) := hD z z.2 hzP
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact Subgroup.mem_normalizer_iff.1 hzD (y : G)
    rcases hirr (D.subgroupOf N) (fun x hx => hDP hx) hNT with h | h
    · have : D ≤ H := fun x hx => h (show (⟨x, hDN hx⟩ : N) ∈ D.subgroupOf N from hx)
      exact hHD'.not_ge this
    · have hH1 : H.subgroupOf N ≤ D.subgroupOf N := fun x hx => hHD hx
      have h2 : D.subgroupOf N = P.subgroupOf N := by
        rw [← h]
        exact (sup_eq_left.2 hH1).symm
      have : P ≤ D := fun x hx => by
        have hx' : (⟨x, hPN hx⟩ : N) ∈ P.subgroupOf N := hx
        rw [← h2] at hx'
        exact hx'
      exact hDPlt.not_ge this

theorem dtopP2_of_class (hc : CFSG.Assembly.IsCharTwoType G)
    {P : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hcl : ClassLETwo P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → z * z = 1) : DtopP2 P := by
  intro H hH
  obtain ⟨M, hHM, hM⟩ := exists_maximal_ge_of_wellFoundedGT (GomiHIn P) H ⟨hH.1.1, hH.2⟩
  have hMS : M ∈ {D : Subgroup G | GomiD P D ∧ H ≤ D} := ⟨hM, hHM⟩
  have h1 : Dtop P ≤ sInf {D : Subgroup G | GomiD P D ∧ H ≤ D} :=
    sInf_le_sInf fun D hD => hD.1
  have hHD : H ≤ sInf {D : Subgroup G | GomiD P D ∧ H ≤ D} := le_sInf fun D hD => hD.2
  have hDP : sInf {D : Subgroup G | GomiD P D ∧ H ≤ D} ≤ P := (sInf_le hMS).trans hM.1.2
  have hnorm : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) → g ∈ Subgroup.normalizer (P : Set G) →
      g ∈ Subgroup.normalizer
        ((sInf {D : Subgroup G | GomiD P D ∧ H ≤ D} : Subgroup G) : Set G) := by
    intro g hgH hgP
    apply Gomi41.mem_normalizer_of_forall_conj_mem
    intro d hd
    refine Subgroup.mem_sInf.2 fun D hD => ?_
    have hD' : D.map (MulAut.conj g⁻¹).toMonoidHom ∈
        {D : Subgroup G | GomiD P D ∧ H ≤ D} := by
      refine ⟨?_, ?_⟩
      · have hPc : P.map (MulAut.conj g⁻¹).toMonoidHom = P :=
          Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ hgP)
        have := hD.1.map_conj g⁻¹
        rwa [hPc] at this
      · have hHc : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
          Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ hgH)
        rw [← hHc]
        exact Subgroup.map_mono hD.2
    exact mem_map_conj_inv_iff'.1 (Subgroup.mem_sInf.1 hd _ hD')
  rcases eq_or_eq_of_normalized hc hP hcl hZ hH.1 hH.2 hHD hDP hnorm with h | h
  · rw [h] at h1
    exact h1
  · exfalso
    have hPM : P ≤ M := h ▸ sInf_le hMS
    exact (GomiD.lt hP hM).not_ge hPM

theorem exists_isOtherSylow {P D : Subgroup G} (hD : GomiD P D) :
    ∃ R : Subgroup G, IsOtherSylow P D R := by
  have hnc := hD.1.1.not_twoClosed
  rw [twoClosed_iff_forall_eq] at hnc
  push Not at hnc
  obtain ⟨S₁, S₂, h₁, h₂, hne⟩ := hnc
  by_cases h : S₁ = P ⊓ Subgroup.normalizer (D : Set G)
  · exact ⟨S₂, h₂, fun h' => hne (h.trans h'.symm)⟩
  · exact ⟨S₁, h₁, h⟩

omit [Finite G] in
theorem gomiE'_symm {P D₁ D₂ : Subgroup G} (h : GomiE' P D₁ D₂) : GomiE' P D₂ D₁ :=
  ⟨GomiE.symm h.1, fun Q₂ Q₁ h₂ h₁ => (h.2 Q₁ Q₂ h₁ h₂).symm⟩

omit [Finite G] in
theorem omegaOneCenterIn_le_of_le (hc : CFSG.Assembly.IsCharTwoType G) {D R : Subgroup G}
    (hD : GomiH D) (hDR : D ≤ R) : omegaOneCenterIn R ≤ D := by
  intro x hx
  obtain ⟨hxR, hxc, -⟩ := mem_omegaOneCenterIn_iff.1 hx
  exact GomiH.center_le hc hD hDR ⟨hxR, Subgroup.mem_centralizer_iff.2 hxc⟩

omit [Finite G] in
theorem isElemAbelian_omegaOneCenterIn (Q : Subgroup G) :
    CFSG.Open.IsElemAbelian 2 (omegaOneCenterIn Q) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨hxQ, -, -⟩ := mem_omegaOneCenterIn_iff.1 x.2
    obtain ⟨-, hyc, -⟩ := mem_omegaOneCenterIn_iff.1 y.2
    exact hyc _ hxQ
  · obtain ⟨-, -, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
    rw [pow_two]
    exact hx2

omit [Finite G] in
theorem isElemAbelian_sup {A B : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.Open.IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

theorem no_gomiE' (hF : Gomi46Facts G) (hc : CFSG.Assembly.IsCharTwoType G) {P : Subgroup G}
    (hP : IsSylowOf 2 P ⊤) (hcl : ClassLETwo P) {D₁ D₂ Q₁ Q₂ : Subgroup G}
    (hD₁ : GomiD P D₁) (hD₂ : GomiD P D₂) (hne : D₁ ≠ D₂) (hQ₁ : IsOtherSylow P D₁ Q₁)
    (hQ₂ : IsOtherSylow P D₂ Q₂) (hX₂ : omegaOneCenterIn Q₂ ≤ D₁) {E₁ E₂ : Subgroup G}
    (hE : GomiE' P E₁ E₂) : False := by
  have hPN : ∀ H : Subgroup G, GomiH H → H ≤ P → P ≤ Subgroup.normalizer (H : Set G) :=
    fun H hH hHP => hH.le_normalizer_of_classLETwo hc hcl hHP
  have hD₁Q₁ : D₁ ≤ Q₁ :=
    le_of_isSylowOf_of_normal hQ₁.1 Subgroup.le_normalizer le_rfl hD₁.1.1.isPGroup
  have hD₂Q₂ : D₂ ≤ Q₂ :=
    le_of_isSylowOf_of_normal hQ₂.1 Subgroup.le_normalizer le_rfl hD₂.1.1.isPGroup
  have hX₁D₁ : omegaOneCenterIn Q₁ ≤ D₁ := omegaOneCenterIn_le_of_le hc hD₁.1.1 hD₁Q₁
  have hX₂D₂ : omegaOneCenterIn Q₂ ≤ D₂ := omegaOneCenterIn_le_of_le hc hD₂.1.1 hD₂Q₂
  have hYab : CFSG.Open.IsElemAbelian 2 (omegaOneCenterIn Q₁ ⊔ omegaOneCenterIn Q₂) :=
    isElemAbelian_sup (isElemAbelian_omegaOneCenterIn Q₁) (isElemAbelian_omegaOneCenterIn Q₂)
      fun a ha b hb => by
        obtain ⟨-, hac, -⟩ := mem_omegaOneCenterIn_iff.1 ha
        exact (hac b (hD₁Q₁ (hX₂ hb))).symm
  have hYP : omegaOneCenterIn Q₁ ⊔ omegaOneCenterIn Q₂ ≤ P :=
    sup_le (hX₁D₁.trans hD₁.1.2) (hX₂D₂.trans hD₂.1.2)
  have sub : ∀ E₁ E₂ : Subgroup G, GomiE' P E₁ E₂ →
      omegaOneCenterIn Q₁ ⊔ omegaOneCenterIn Q₂ ≤ E₁ → False := by
    intro E₁ E₂ hE hY
    have hE₁ : GomiD P E₁ := hE.1.1
    have hPE₁ : P ≤ Subgroup.normalizer (E₁ : Set G) := hPN E₁ hE₁.1.1 hE₁.1.2
    have key : ∀ a Qa : Subgroup G, GomiD P a → IsOtherSylow P a Qa → a ≠ E₁ →
        omegaOneCenterIn Qa ≤ E₁ → False := by
      intro a Qa ha hQa hane hXa
      have hPa : P ≤ Subgroup.normalizer (a : Set G) := hPN a ha.1.1 ha.1.2
      have hpair : GomiE P a E₁ :=
        ⟨ha, hE₁, hane, by rw [inf_eq_left.2 hPa, inf_eq_left.2 hPE₁], Or.inl ⟨hPa, hPE₁⟩⟩
      obtain ⟨R₁, hR₁⟩ := exists_isOtherSylow hE₁
      have hXR : omegaOneCenterIn R₁ ≤ a :=
        (hF.l45_three P a E₁ Qa R₁ hP hpair hQa hR₁).1 hXa
      have h2 := hF.l46_two P E₁ E₂ R₁ hP hE hR₁
      have haPN : a ≤ P ⊓ Subgroup.normalizer (E₁ : Set G) :=
        le_inf ha.1.2 (ha.1.2.trans hPE₁)
      have hXP : omegaOneCenterIn (P ⊓ Subgroup.normalizer (E₁ : Set G)) ≤ a :=
        omegaOneCenterIn_le_of_le hc ha.1.1 haPN
      have hEa : E₁ ≤ a := by
        calc E₁ = omegaOneCenterIn R₁ ⊔
            omegaOneCenterIn (P ⊓ Subgroup.normalizer (E₁ : Set G)) := h2
          _ ≤ a := sup_le hXR hXP
      exact hane (le_antisymm (hE₁.2 ha.1 hEa) hEa)
    by_cases hD : D₁ = E₁
    · exact key D₂ Q₂ hD₂ hQ₂ (fun h => hne (hD.trans h.symm)) (le_sup_right.trans hY)
    · exact key D₁ Q₁ hD₁ hQ₁ hD (le_sup_left.trans hY)
  have hE₁ : GomiD P E₁ := hE.1.1
  have hPE₁ : P ≤ Subgroup.normalizer (E₁ : Set G) := hPN E₁ hE₁.1.1 hE₁.1.2
  rcases hF.l46_four P E₁ E₂ _ hP hE (le_inf hYP (hYP.trans hPE₁)) hYab with hY | hY
  · exact sub E₁ E₂ hE hY
  · exact sub E₂ E₁ (gomiE'_symm hE) hY

@[expose] def Good47 (P : Subgroup G) : Prop :=
  ∀ Di Dj R : Subgroup G, GomiD P Di → GomiD P Dj → Di ≠ Dj → IsOtherSylow P Di R →
    omegaOneCenterIn R ≤ Dj

omit [Finite G] in
theorem good47_of_no_gomiE' (hF : Gomi46Facts G) {P : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hPN : ∀ H : Subgroup G, GomiH H → H ≤ P → P ≤ Subgroup.normalizer (H : Set G))
    (hno : ∀ E₁ E₂ : Subgroup G, ¬ GomiE' P E₁ E₂) : Good47 P := by
  intro Di Dj R hDi hDj hne hR
  have hPi := hPN Di hDi.1.1 hDi.1.2
  have hPj := hPN Dj hDj.1.1 hDj.1.2
  have hpair : GomiE P Di Dj :=
    ⟨hDi, hDj, hne, by rw [inf_eq_left.2 hPi, inf_eq_left.2 hPj], Or.inl ⟨hPi, hPj⟩⟩
  have h1 : ∃ Q₁ Q₂ : Subgroup G, IsOtherSylow P Di Q₁ ∧ IsOtherSylow P Dj Q₂ ∧
      (omegaOneCenterIn Q₁ ≤ Dj ∨ omegaOneCenterIn Q₂ ≤ Di) := by
    by_contra hcon
    push Not at hcon
    exact hno Di Dj ⟨hpair, fun Q₁ Q₂ h₁ h₂ => hcon Q₁ Q₂ h₁ h₂⟩
  obtain ⟨Q₁, Q₂, h₁, h₂, hor⟩ := h1
  have hiff := hF.l45_three P Di Dj Q₁ Q₂ hP hpair h₁ h₂
  have hX₂ : omegaOneCenterIn Q₂ ≤ Di := hor.elim hiff.1 id
  exact (hF.l45_three P Di Dj R Q₂ hP hpair hR h₂).2 hX₂

theorem dtopP1_of_good (hc : CFSG.Assembly.IsCharTwoType G)
    (hcl : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S)
    (hz : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ∀ z ∈ S, (∀ y ∈ S, y * z = z * y) → z * z = 1)
    {P D₁ : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hD₁ : GomiD P D₁) (hgood : Good47 P) :
    DtopP1 P := by
  have hPN : ∀ H : Subgroup G, GomiH H → H ≤ P → P ≤ Subgroup.normalizer (H : Set G) :=
    fun H hH hHP => hH.le_normalizer_of_classLETwo hc (hcl P hP) hHP
  have hDP : Dtop P ≤ P := (Dtop_le hD₁).trans hD₁.1.2
  have hD2 : IsPGroup 2 (Dtop P) := hD₁.1.1.isPGroup.to_le (Dtop_le hD₁)
  have hDne : Dtop P ≠ ⊥ := by
    have hP1 : P ≠ ⊥ := fun h => hD₁.1.1.ne_bot (le_bot_iff.1 (h ▸ hD₁.1.2))
    have hXne : omegaOneCenterIn P ≠ ⊥ := omegaOneCenterIn_ne_bot hP.isPGroup hP1
    have hXD : omegaOneCenterIn P ≤ Dtop P :=
      le_Dtop fun D hD => omegaOneCenterIn_le_of_le hc hD.1.1 hD.1.2
    exact fun h => hXne (le_bot_iff.1 (h ▸ hXD))
  have hPND : P ≤ Subgroup.normalizer (Dtop P : Set G) := by
    intro x hx
    apply Gomi41.mem_normalizer_of_forall_conj_mem
    intro d hd
    refine Subgroup.mem_sInf.2 fun Di hDi => ?_
    exact (Subgroup.mem_normalizer_iff.1 (hPN Di hDi.1.1 hDi.1.2 hx) d).1
      (Subgroup.mem_sInf.1 hd Di hDi)
  have hRN : ∀ Di R : Subgroup G, GomiD P Di → IsOtherSylow P Di R →
      R ≤ Subgroup.normalizer (Dtop P : Set G) := by
    intro Di R hDi hR y hy
    have hDiR : Di ≤ R :=
      le_of_isSylowOf_of_normal hR.1 Subgroup.le_normalizer le_rfl hDi.1.1.isPGroup
    have hRsyl : IsSylowOf 2 R ⊤ := isSylowOf_top_of_le hP (hPN Di hDi.1.1 hDi.1.2) hR.1
    have hRcl := hcl R hRsyl
    apply Gomi41.mem_normalizer_of_forall_conj_mem
    intro d hd
    have hdR : d ∈ R := hDiR (Dtop_le hDi hd)
    have hycR : ⁅y, d⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hy hdR) (R.inv_mem hy)) (R.inv_mem hdR)
    have hcent : ∀ w ∈ R, w * ⁅y, d⁆ = ⁅y, d⁆ * w := fun w hw =>
      (commutatorElement_eq_one_iff_mul_comm.1 (hRcl y hy d hdR w hw)).symm
    have hXmem : ⁅y, d⁆ ∈ omegaOneCenterIn R :=
      mem_omegaOneCenterIn_iff.2 ⟨hycR, hcent, hz R hRsyl _ hycR hcent⟩
    have hXD : ⁅y, d⁆ ∈ Dtop P := by
      refine Subgroup.mem_sInf.2 fun Dj hDj => ?_
      by_cases hij : Di = Dj
      · subst hij
        exact omegaOneCenterIn_le_of_le hc hDi.1.1 hDiR hXmem
      · exact hgood Di Dj R hDi hDj hij hR hXmem
    have h1 : y * d * y⁻¹ = ⁅y, d⁆ * d := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact (Dtop P).mul_mem hXD hd
  refine ⟨⟨hDne, ?_, ?_⟩, hPND⟩
  ·
    obtain ⟨R, hR⟩ := exists_isOtherSylow hD₁
    have hRsyl : IsSylowOf 2 R ⊤ := isSylowOf_top_of_le hP (hPN D₁ hD₁.1.1 hD₁.1.2) hR.1
    intro hTC
    have heq := twoClosed_iff_forall_eq.1 hTC P R (hP.of_le hPND le_top)
      (hRsyl.of_le (hRN D₁ R hD₁ hR) le_top)
    exact hR.2 (by rw [← heq]; exact (inf_eq_left.2 (hPN D₁ hD₁.1.1 hD₁.1.2)).symm)
  ·
    refine le_antisymm ?_ (le_oTwoIn_of_normal Subgroup.le_normalizer le_rfl hD2)
    refine le_Dtop fun Di hDi => ?_
    obtain ⟨R, hR⟩ := exists_isOtherSylow hDi
    have hPDi := hPN Di hDi.1.1 hDi.1.2
    have hRsyl : IsSylowOf 2 R ⊤ := isSylowOf_top_of_le hP hPDi hR.1
    have hRs : IsSylowOf 2 R (Subgroup.normalizer (Dtop P : Set G)) :=
      hRsyl.of_le (hRN Di R hDi hR) le_top
    have hPs : IsSylowOf 2 P (Subgroup.normalizer (Dtop P : Set G)) := hP.of_le hPND le_top
    have hne : P ≠ R := fun h => hR.2 (by rw [← h]; exact (inf_eq_left.2 hPDi).symm)
    have hinf := hDi.inf_eq hP (hP.of_le hPDi le_top) hR.1 hne
    exact (le_inf (oTwoIn_le_of_isSylowOf hPs) (oTwoIn_le_of_isSylowOf hRs)).trans hinf.le

@[expose] def omegaInv (Δ : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ Δ ∧ x * x = 1}

omit [Finite G] in
theorem omegaInv_le (Δ : Subgroup G) : omegaInv Δ ≤ Δ :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

omit [Finite G] in
theorem mem_omegaInv_of {Δ : Subgroup G} {x : G} (hx : x ∈ Δ) (hx2 : x * x = 1) :
    x ∈ omegaInv Δ :=
  Subgroup.subset_closure ⟨hx, hx2⟩

theorem normalizer_le_normalizer_omegaInv (Δ : Subgroup G) :
    Subgroup.normalizer (Δ : Set G) ≤ Subgroup.normalizer (omegaInv Δ : Set G) := by
  intro q hq
  apply Gomi41.mem_normalizer_of_forall_conj_mem
  intro d hd
  refine Subgroup.closure_induction (p := fun z _ => q * z * q⁻¹ ∈ omegaInv Δ) ?_ ?_ ?_ ?_ hd
  · rintro z ⟨hzΔ, hz2⟩
    refine mem_omegaInv_of ((Subgroup.mem_normalizer_iff.1 hq z).1 hzΔ) ?_
    calc q * z * q⁻¹ * (q * z * q⁻¹) = q * (z * z) * q⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  · simp
  · intro y z _ _ hy hz
    have : q * (y * z) * q⁻¹ = (q * y * q⁻¹) * (q * z * q⁻¹) := by group
    rw [this]
    exact (omegaInv Δ).mul_mem hy hz
  · intro y _ hy
    have : q * y⁻¹ * q⁻¹ = (q * y * q⁻¹)⁻¹ := by group
    rw [this]
    exact (omegaInv Δ).inv_mem hy

omit [Finite G] in
theorem commutator_mem_omegaOneCenterIn {R Δ : Subgroup G} (hRcl : ClassLETwo R) (hΔR : Δ ≤ R)
    {d : G} (hd : d ∈ omegaInv Δ) : d ∈ R ∧ ∀ y ∈ R, ⁅y, d⁆ ∈ omegaOneCenterIn R := by
  have hcR : ∀ y ∈ R, ∀ z ∈ R, ⁅y, z⁆ ∈ R := fun y hy z hz => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hy hz) (R.inv_mem hy)) (R.inv_mem hz)
  have hcent : ∀ y ∈ R, ∀ z ∈ R, ∀ w ∈ R, w * ⁅y, z⁆ = ⁅y, z⁆ * w := fun y hy z hz w hw =>
    (commutatorElement_eq_one_iff_mul_comm.1 (hRcl y hy z hz w hw)).symm
  refine Subgroup.closure_induction
    (p := fun z _ => z ∈ R ∧ ∀ y ∈ R, ⁅y, z⁆ ∈ omegaOneCenterIn R) ?_ ?_ ?_ ?_ hd
  · rintro z ⟨hzΔ, hz2⟩
    have hzR : z ∈ R := hΔR hzΔ
    refine ⟨hzR, fun y hy => ?_⟩
    obtain ⟨c, hc⟩ : ∃ c : G, c = ⁅y, z⁆ := ⟨_, rfl⟩
    have hcR' : c ∈ R := hc ▸ hcR y hy z hzR
    have hcc : ∀ w ∈ R, w * c = c * w := hc ▸ hcent y hy z hzR
    have h1 : y * z * y⁻¹ = c * z := by rw [hc, commutatorElement_def]; group
    have h2 : z * c = c * z := hcc z hzR
    have h3 : c * c = 1 := by
      calc c * c = c * c * (z * z) := by rw [hz2, mul_one]
        _ = c * (c * z) * z := by group
        _ = c * (z * c) * z := by rw [h2]
        _ = (c * z) * (c * z) := by group
        _ = (y * z * y⁻¹) * (y * z * y⁻¹) := by rw [h1]
        _ = y * (z * z) * y⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rw [← hc]
    exact mem_omegaOneCenterIn_iff.2 ⟨hcR', hcc, h3⟩
  · refine ⟨R.one_mem, fun y _ => ?_⟩
    simp
  · rintro a b _ _ ⟨haR, ha⟩ ⟨hbR, hb⟩
    refine ⟨R.mul_mem haR hbR, fun y hy => ?_⟩
    have hcb : a * ⁅y, b⁆ = ⁅y, b⁆ * a := hcent y hy b hbR a haR
    have e : ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆ := by
      calc ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by simp only [commutatorElement_def]; group
        _ = ⁅y, a⁆ * ⁅y, b⁆ := by rw [hcb]; group
    rw [e]
    exact (omegaOneCenterIn R).mul_mem (ha y hy) (hb y hy)
  · rintro a _ ⟨haR, ha⟩
    refine ⟨R.inv_mem haR, fun y hy => ?_⟩
    obtain ⟨c, hc⟩ : ∃ c : G, c = ⁅y, a⁆ := ⟨_, rfl⟩
    have hca : a⁻¹ * c = c * a⁻¹ := hc ▸ hcent y hy a haR a⁻¹ (R.inv_mem haR)
    have hca' : a⁻¹ * c⁻¹ = c⁻¹ * a⁻¹ := by
      calc a⁻¹ * c⁻¹ = c⁻¹ * (c * a⁻¹) * c⁻¹ := by group
        _ = c⁻¹ * (a⁻¹ * c) * c⁻¹ := by rw [hca]
        _ = c⁻¹ * a⁻¹ := by group
    have e : ⁅y, a⁻¹⁆ = c⁻¹ := by
      calc ⁅y, a⁻¹⁆ = a⁻¹ * c⁻¹ * a := by rw [hc]; simp only [commutatorElement_def]; group
        _ = c⁻¹ * a⁻¹ * a := by rw [hca']
        _ = c⁻¹ := by group
    rw [e, hc]
    exact (omegaOneCenterIn R).inv_mem (ha y hy)

omit [Finite G] in
theorem classLETwo_map_conj {S : Subgroup G} (h : ClassLETwo S) (g : G) :
    ClassLETwo (S.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
  rw [← map_commutatorElement, ← map_commutatorElement, h a ha b hb c hc, map_one]

theorem le_normalizer_of_bad (hA : GomiAmbient G) {P D₁ D₂ Q₁ : Subgroup G}
    (hP : IsSylowOf 2 P ⊤) (hE : GomiE P D₁ D₂) (hQ₁ : IsOtherSylow P D₁ Q₁)
    (hX₁ : omegaOneCenterIn Q₁ ≤ D₂) : P ≤ Subgroup.normalizer (D₁ : Set G) := by
  by_contra hPnot
  have hc := hA.charTwo
  obtain ⟨hD₁, hD₂, hne, hNeq, hcase⟩ := hE
  obtain ⟨u, huP, hu1, hu2⟩ : ∃ u ∈ P, D₁.map (MulAut.conj u).toMonoidHom = D₂ ∧
      D₂.map (MulAut.conj u).toMonoidHom = D₁ := by
    rcases hcase with ⟨h1, -⟩ | h
    · exact absurd h1 hPnot
    · exact h
  have hg₁ : GomiH D₁ := hD₁.1.1
  have hD₁Q₁ : D₁ ≤ Q₁ :=
    le_of_isSylowOf_of_normal hQ₁.1 Subgroup.le_normalizer le_rfl hg₁.isPGroup
  have hQ₁cl : ClassLETwo Q₁ := hA.classTwo _ hg₁.isTwoLocal hg₁.not_twoClosed Q₁ hQ₁.1
  have hX₁D₁ : omegaOneCenterIn Q₁ ≤ D₁ := omegaOneCenterIn_le_of_le hc hg₁ hD₁Q₁
  have hΔQ₁ : D₁ ⊓ D₂ ≤ Q₁ := inf_le_left.trans hD₁Q₁
  have hX₁Dm : omegaOneCenterIn Q₁ ≤ omegaInv (D₁ ⊓ D₂) := fun x hx => by
    obtain ⟨-, -, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
    exact mem_omegaInv_of ⟨hX₁D₁ hx, hX₁ hx⟩ hx2
  have hQ₁N : Q₁ ≤ Subgroup.normalizer (omegaInv (D₁ ⊓ D₂) : Set G) := by
    intro y hy
    apply Gomi41.mem_normalizer_of_forall_conj_mem
    intro d hd
    have hc' := (commutator_mem_omegaOneCenterIn hQ₁cl hΔQ₁ hd).2 y hy
    have e : y * d * y⁻¹ = ⁅y, d⁆ * d := by rw [commutatorElement_def]; group
    rw [e]
    exact (omegaInv (D₁ ⊓ D₂)).mul_mem (hX₁Dm hc') hd
  have hQΔ : P ⊓ Subgroup.normalizer (D₁ : Set G) ≤
      Subgroup.normalizer ((D₁ ⊓ D₂ : Subgroup G) : Set G) := by
    intro q hq
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.1 hq.2
    have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hNeq.le hq).2
    apply Subgroup.mem_normalizer_iff_map_conj_eq.2
    rw [Subgroup.map_inf _ _ _ (MulAut.conj q).injective, h1, h2]
  have hQN : P ⊓ Subgroup.normalizer (D₁ : Set G) ≤
      Subgroup.normalizer (omegaInv (D₁ ⊓ D₂) : Set G) :=
    fun q hq => normalizer_le_normalizer_omegaInv _ (hQΔ hq)
  have hDmne : omegaInv (D₁ ⊓ D₂) ≠ ⊥ := by
    have hQ₁ne : Q₁ ≠ ⊥ := fun h => hg₁.ne_bot (le_bot_iff.1 (h ▸ hD₁Q₁))
    have hXne : omegaOneCenterIn Q₁ ≠ ⊥ := omegaOneCenterIn_ne_bot hQ₁.1.isPGroup hQ₁ne
    exact fun h => hXne (le_bot_iff.1 (h ▸ hX₁Dm))
  have hDm2 : IsPGroup 2 (omegaInv (D₁ ⊓ D₂)) :=
    hg₁.isPGroup.to_le ((omegaInv_le _).trans inf_le_left)
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (omegaInv (D₁ ⊓ D₂) : Set G)) :=
    ⟨_, hDmne, hDm2, rfl⟩
  have hnc : ¬ TwoClosed (Subgroup.normalizer (omegaInv (D₁ ⊓ D₂) : Set G)) := by
    intro hTC
    obtain ⟨S₁, hS₁, hQS⟩ := exists_isSylowOf_ge hQN hP.isPGroup.to_inf_left
    obtain ⟨S₂, hS₂, hQ₁S⟩ := exists_isSylowOf_ge hQ₁N hQ₁.1.isPGroup
    have hSS : S₁ = S₂ := twoClosed_iff_forall_eq.1 hTC _ _ hS₁ hS₂
    have hQsyl : IsSylowOf 2 (P ⊓ Subgroup.normalizer (D₁ : Set G))
        (Subgroup.normalizer (D₁ : Set G)) := hD₁.isSylowOf_inf_normalizer hP
    have e1 : S₁ ⊓ Subgroup.normalizer (D₁ : Set G) = P ⊓ Subgroup.normalizer (D₁ : Set G) :=
      hQsyl.eq_of_le (le_inf hQS inf_le_right) inf_le_right hS₁.isPGroup.to_inf_left
    have e2 : S₁ ⊓ Subgroup.normalizer (D₁ : Set G) = Q₁ :=
      hQ₁.1.eq_of_le (le_inf (hSS ▸ hQ₁S) hQ₁.1.le) inf_le_right hS₁.isPGroup.to_inf_left
    exact hQ₁.2 (e2.symm.trans e1)
  have hRcl : ClassLETwo (P ⊓ Subgroup.normalizer (omegaInv (D₁ ⊓ D₂) : Set G)) :=
    hA.classLETwo_of_le hloc hnc inf_le_right hP.isPGroup.to_inf_left
  have hD₁R : D₁ ≤ P ⊓ Subgroup.normalizer (omegaInv (D₁ ⊓ D₂) : Set G) :=
    le_inf hD₁.1.2 fun x hx => hQN ⟨hD₁.1.2 hx, Subgroup.le_normalizer hx⟩
  have hRQ : P ⊓ Subgroup.normalizer (omegaInv (D₁ ⊓ D₂) : Set G) ≤
      P ⊓ Subgroup.normalizer (D₁ : Set G) :=
    le_inf inf_le_left (GomiH.le_normalizer_of_classLETwo hc hg₁ hRcl hD₁R)
  have hu : u ∈ Subgroup.normalizer ((D₁ ⊓ D₂ : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.2
    have e : (D₁ ⊓ D₂).map (MulAut.conj u).toMonoidHom = D₁ ⊓ D₂ := by
      rw [Subgroup.map_inf D₁ D₂ (MulAut.conj u).toMonoidHom (MulAut.conj u).injective, hu1, hu2,
        inf_comm]
    exact e
  have huQ : u ∈ P ⊓ Subgroup.normalizer (D₁ : Set G) :=
    hRQ ⟨huP, normalizer_le_normalizer_omegaInv _ hu⟩
  have h1 : D₁.map (MulAut.conj u).toMonoidHom = D₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 huQ.2
  exact hne (by rw [← hu1, h1])

theorem false_of_bad_pair (hF : Gomi46Facts G)
    (hc : CFSG.Assembly.IsCharTwoType G) (hcl : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S)
    (hz : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ∀ z ∈ S, (∀ y ∈ S, y * z = z * y) → z * z = 1)
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) {P D₁ D₂ Q₁ Q₂ : Subgroup G}
    (hP : IsSylowOf 2 P ⊤) (hD₁ : GomiD P D₁) (hD₂ : GomiD P D₂) (hne : D₁ ≠ D₂)
    (hQ₁ : IsOtherSylow P D₁ Q₁) (hQ₂ : IsOtherSylow P D₂ Q₂)
    (hX₂ : omegaOneCenterIn Q₂ ≤ D₁) : False := by
  have hPN : ∀ H : Subgroup G, GomiH H → H ≤ P → P ≤ Subgroup.normalizer (H : Set G) :=
    fun H hH hHP => hH.le_normalizer_of_classLETwo hc (hcl P hP) hHP
  have hno : ∀ E₁ E₂ : Subgroup G, ¬ GomiE' P E₁ E₂ := fun E₁ E₂ hE =>
    no_gomiE' hF hc hP (hcl P hP) hD₁ hD₂ hne hQ₁ hQ₂ hX₂ hE
  have hgood := good47_of_no_gomiE' hF hP hPN hno
  have h1 := dtopP1_of_good hc hcl hz hP hD₁ hgood
  have h2 := dtopP2_of_class hc hP (hcl P hP) (hz P hP)
  have hall : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → DtopP1 S ∧ DtopP2 S :=
    fun S hS => dtopP12_of_sylow hP hS h1 h2
  exact false_of_invariant_assignment hO hO2 Dtop hP h1.1 ((Dtop_le hD₁).trans hD₁.1.2) h1.2
    (fun S _ g => Dtop_map_conj S g)
    (fun A B hA hB h => Dtop_eq_of_inf_ne_bot hc hcl hall hA hB h)

end Gomi47

theorem gomiE'_of_gomiE [Finite G] (hA : GomiAmbient G)
    (hF : Gomi46Facts G) (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) {P D₁ D₂ : Subgroup G}
    (hP : IsSylowOf 2 P ⊤) (hE : GomiE P D₁ D₂) : GomiE' P D₁ D₂ := by
  refine ⟨hE, fun Q₁ Q₂ hQ₁ hQ₂ => ?_⟩
  have hiff := hF.l45_three P D₁ D₂ Q₁ Q₂ hP hE hQ₁ hQ₂
  by_contra hbad
  have hX₂ : omegaOneCenterIn Q₂ ≤ D₁ := by
    by_contra h2
    exact hbad ⟨fun h1 => h2 (hiff.1 h1), h2⟩
  have hX₁ : omegaOneCenterIn Q₁ ≤ D₂ := hiff.2 hX₂
  have hPN : P ≤ Subgroup.normalizer (D₁ : Set G) :=
    Gomi47.le_normalizer_of_bad hA hP hE hQ₁ hX₁
  have hg₁ : GomiH D₁ := hE.1.1.1
  have hclP : ClassLETwo P :=
    hA.classTwo _ hg₁.isTwoLocal hg₁.not_twoClosed P (hP.of_le hPN le_top)
  have hcl : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ClassLETwo S := fun S hS => by
    obtain ⟨g, -, hg⟩ := exists_eq_map_conj_of_isSylowOf hP hS
    rw [hg]
    exact Gomi47.classLETwo_map_conj hclP g
  have hz : ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ∀ z ∈ S, (∀ y ∈ S, y * z = z * y) → z * z = 1 :=
    fun S hS z hz hzc => hA.zElem S hS (hcl S hS) z ⟨hz, Subgroup.mem_centralizer_iff.2 hzc⟩
  exact Gomi47.false_of_bad_pair hF hA.charTwo hcl hz hO hO2 hP hE.1 hE.2.1 hE.2.2.1 hQ₁ hQ₂ hX₂

end CFSG.CGT.PushingUpLit.C2L
