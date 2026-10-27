module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2b1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2b2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2c1

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {φ : (Fin 5 → ZMod 2) → G}

theorem sec1011_phi_zero (hs : Sec1011Setup t L S z φ) : φ 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by
    unfold IsEvenVec
    simp
  have h := hs.hperm.1 0 0 h0 h0
  rw [add_zero] at h
  have h' : φ 0 * φ 0 = φ 0 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h'

theorem sec1011_B_sq (hs : Sec1011Setup t L S z φ) : ∀ b ∈ secB S L, b * b = 1 := by
  intro b hb
  obtain ⟨v, hv, rfl⟩ := (hs.hperm.2.2.1 b).1 hb
  rw [← hs.hperm.1 v v hv hv, sec1011_vec_add_self, sec1011_phi_zero hs]

theorem sec1011_sq_mem_of_relIndex_le_two [Finite G] {H N : Subgroup G}
    (hle : H.relIndex N ≤ 2) {x : G} (hx : x ∈ N) : x ^ 2 ∈ H := by
  have hne : (H.subgroupOf N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle' : (H.subgroupOf N).index ≤ 2 := hle
  have hmem : (⟨x, hx⟩ : ↥N) ^ 2 ∈ H.subgroupOf N := by
    rcases (by omega : (H.subgroupOf N).index = 1 ∨ (H.subgroupOf N).index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top _
    · exact Subgroup.sq_mem_of_index_two h2 _
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem sec1011_conj_mem_cent {y h m : G} (hh : h * y * h⁻¹ = t)
    (hm : m * y = y * m) : h * m * h⁻¹ ∈ centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← hh]
  calc h * m * h⁻¹ * (h * y * h⁻¹) = h * (m * y) * h⁻¹ := by group
    _ = h * (y * m) * h⁻¹ := by rw [hm]
    _ = h * y * h⁻¹ * (h * m * h⁻¹) := by group

private def sec1011_cs (B : Subgroup G) (h : G) : Subgroup G :=
  B.map (MulAut.conj h).toMonoidHom

private theorem sec1011_mem_cs {B : Subgroup G} {h x : G} :
    x ∈ sec1011_cs B h ↔ h⁻¹ * x * h ∈ B := by
  unfold sec1011_cs
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have e : h⁻¹ * (h * b * h⁻¹) * h = b := by group
    rw [e]
    exact hb
  · intro hx
    exact ⟨h⁻¹ * x * h, hx, by group⟩

private theorem sec1011_card_cs (B : Subgroup G) (h : G) :
    Nat.card (sec1011_cs B h) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj h).injective

private theorem sec1011_cs_normalizer {B : Subgroup G} {n : G} (hn : n ∈ normalizer (B : Set G))
    (h : G) : h * n * h⁻¹ ∈ normalizer (sec1011_cs B h : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [sec1011_mem_cs, sec1011_mem_cs]
  have e : h⁻¹ * (h * n * h⁻¹ * x * (h * n * h⁻¹)⁻¹) * h = n * (h⁻¹ * x * h) * n⁻¹ := by
    group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hn (h⁻¹ * x * h)

theorem sec1011_p2_conj_false [Finite G] (hB5 : Asc82FactB5) (hOut5 : Asc82FactOut5)
    (hpsp : IsPSp43 L) (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (h102 : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G))))
    (hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hB16 : Nat.card (secB S L) = 2 ^ 4) (hs : Sec1011Setup t L S z φ)
    (h6 : sec1011_orb (secMstar t S L) (sec1011_tA t S L) =
      {a | a = sec1011_tA t S L ∨ ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧
        a = sec1011_tA t S L * sec1011_phiA t S L φ v})
    (h107b : Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5)))
    {h : G} (hh : h * (t * φ sec1011_w0) * h⁻¹ = t) : False := by
  obtain ⟨n1, hn1M, n2, hn2M, hf1, hf2, hcc, hc1, hc2, hspan⟩ := sec1011_p2_lift hs h6 h107b
  have hw0B : φ sec1011_w0 ∈ secB S L := sec1011_phi_mem_B hs sec1011_w0_even
  have hMB : ∀ n ∈ secM t S L, n ∈ normalizer (secB S L : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨fun hb => hs.hBM n hn b hb, fun hb => ?_⟩
    have h' := hs.hBM n⁻¹ ((secM t S L).inv_mem hn) _ hb
    have e : n⁻¹ * (n * b * n⁻¹) * n⁻¹⁻¹ = b := by group
    rwa [e] at h'
  have hBy : ∀ b ∈ secB S L, b * (t * φ sec1011_w0) = (t * φ sec1011_w0) * b := by
    intro b hb
    have h1 := sec1011_B_t_comm hs b hb
    have h2 := sec1011_B_comm hs b hb _ hw0B
    calc b * (t * φ sec1011_w0) = (b * t) * φ sec1011_w0 := by group
      _ = (t * b) * φ sec1011_w0 := by rw [h1]
      _ = t * (b * φ sec1011_w0) := by group
      _ = t * (φ sec1011_w0 * b) := by rw [h2]
      _ = (t * φ sec1011_w0) * b := by group
  have hcy : ∀ n : G, n * (t * φ sec1011_w0) * n⁻¹ = t * φ sec1011_w0 →
      n ^ 4 * (t * φ sec1011_w0) = (t * φ sec1011_w0) * n ^ 4 := fun n hn =>
    (Commute.pow_left (mul_inv_eq_iff_eq_mul.mp hn) 4).eq
  have hgen : ∀ n ∈ secM t S L, n * (t * φ sec1011_w0) * n⁻¹ = t * φ sec1011_w0 →
      h * n ^ 4 * h⁻¹ ∈ normalizer (L : Set G) ∧
      h * n ^ 4 * h⁻¹ ∈ normalizer (sec1011_cs (secB S L) h : Set G) ∧
      h * n ^ 4 * h⁻¹ ∈ L ⊔ centralizer (L : Set G) := by
    intro n hnM hn
    refine ⟨hN (sec1011_conj_mem_cent hh (hcy n hn)),
      sec1011_cs_normalizer (hMB (n ^ 4) ((secM t S L).pow_mem hnM 4)) h, ?_⟩
    have hm : h * n * h⁻¹ ∈ normalizer (L : Set G) :=
      hN (sec1011_conj_mem_cent hh (mul_inv_eq_iff_eq_mul.mp hn))
    have h2 := sec1011_sq_mem_of_relIndex_le_two (hOut5 G L hpsp)
      ((normalizer (L : Set G)).pow_mem hm 2)
    have e : h * n ^ 4 * h⁻¹ = ((h * n * h⁻¹) ^ 2) ^ 2 := by
      rw [← pow_mul, conj_pow]
    rw [e]
    exact h2
  obtain ⟨hc1N, hc1B, hc1LC⟩ := hgen n1 hn1M hf1
  obtain ⟨hc2N, hc2B, hc2LC⟩ := hgen n2 hn2M hf2
  have hd : Sec1011P2Data L (sec1011_cs (secB S L) h) (h * n1 ^ 4 * h⁻¹) (h * n2 ^ 4 * h⁻¹) := by
    refine { card := ?_, comm := ?_, sq := ?_, normL := ?_, c1N := hc1N, c2N := hc2N,
             c1B := hc1B, c2B := hc2B, c1LC := hc1LC, c2LC := hc2LC, cc := ?_, cube1 := ?_,
             cube2 := ?_, span := ?_ }
    · rw [sec1011_card_cs]
      exact hB16
    · intro a ha b hb
      rw [sec1011_mem_cs] at ha hb
      have e := sec1011_B_comm hs _ ha _ hb
      calc a * b = h * (h⁻¹ * a * h * (h⁻¹ * b * h)) * h⁻¹ := by group
        _ = h * (h⁻¹ * b * h * (h⁻¹ * a * h)) * h⁻¹ := by rw [e]
        _ = b * a := by group
    · intro b hb
      rw [sec1011_mem_cs] at hb
      have e := sec1011_B_sq hs _ hb
      calc b * b = h * (h⁻¹ * b * h * (h⁻¹ * b * h)) * h⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro x hx
      rw [sec1011_mem_cs] at hx
      have hx' := hN (sec1011_conj_mem_cent hh (hBy _ hx))
      have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rwa [e] at hx'
    · intro b hb
      rw [sec1011_mem_cs] at hb
      have e := hcc _ hb
      calc h * n1 ^ 4 * h⁻¹ * (h * n2 ^ 4 * h⁻¹ * b * (h * n2 ^ 4 * h⁻¹)⁻¹) *
            (h * n1 ^ 4 * h⁻¹)⁻¹
          = h * (n1 ^ 4 * (n2 ^ 4 * (h⁻¹ * b * h) * (n2 ^ 4)⁻¹) * (n1 ^ 4)⁻¹) * h⁻¹ := by
            group
        _ = h * (n2 ^ 4 * (n1 ^ 4 * (h⁻¹ * b * h) * (n1 ^ 4)⁻¹) * (n2 ^ 4)⁻¹) * h⁻¹ := by
            rw [e]
        _ = h * n2 ^ 4 * h⁻¹ * (h * n1 ^ 4 * h⁻¹ * b * (h * n1 ^ 4 * h⁻¹)⁻¹) *
            (h * n2 ^ 4 * h⁻¹)⁻¹ := by group
    · intro b hb
      rw [sec1011_mem_cs] at hb
      have e := hc1 _ hb
      calc (h * n1 ^ 4 * h⁻¹) ^ 3 * b * ((h * n1 ^ 4 * h⁻¹) ^ 3)⁻¹
          = h * ((n1 ^ 4) ^ 3 * (h⁻¹ * b * h) * ((n1 ^ 4) ^ 3)⁻¹) * h⁻¹ := by
            rw [conj_pow]
            group
        _ = b := by rw [e]; group
    · intro b hb
      rw [sec1011_mem_cs] at hb
      have e := hc2 _ hb
      calc (h * n2 ^ 4 * h⁻¹) ^ 3 * b * ((h * n2 ^ 4 * h⁻¹) ^ 3)⁻¹
          = h * ((n2 ^ 4) ^ 3 * (h⁻¹ * b * h) * ((n2 ^ 4) ^ 3)⁻¹) * h⁻¹ := by
            rw [conj_pow]
            group
        _ = b := by rw [e]; group
    · intro b hb
      rw [sec1011_mem_cs] at hb
      obtain ⟨b1, hb1, b2, hb2, hb12⟩ := hspan _ hb
      refine ⟨h * b1 * h⁻¹, ?_, h * b2 * h⁻¹, ?_, ?_⟩
      · rw [sec1011_mem_cs]
        have e : h⁻¹ * (h * b1 * h⁻¹) * h = b1 := by group
        rw [e]
        exact hb1
      · rw [sec1011_mem_cs]
        have e : h⁻¹ * (h * b2 * h⁻¹) * h = b2 := by group
        rw [e]
        exact hb2
      · calc b = h * (h⁻¹ * b * h) * h⁻¹ := by group
          _ = h * (b1 * (n1 ^ 4 * b1 * (n1 ^ 4)⁻¹) * (b2 * (n2 ^ 4 * b2 * (n2 ^ 4)⁻¹))) * h⁻¹ := by
            rw [hb12]
          _ = h * b1 * h⁻¹ * (h * n1 ^ 4 * h⁻¹ * (h * b1 * h⁻¹) * (h * n1 ^ 4 * h⁻¹)⁻¹) *
            (h * b2 * h⁻¹ * (h * n2 ^ 4 * h⁻¹ * (h * b2 * h⁻¹) * (h * n2 ^ 4 * h⁻¹)⁻¹)) := by
            group
  exact sec1011_p2_false hB5 hpsp hd (sec1011_p2_le hLC h102 hd)

end CFSG.OddStandard.SmallF3.Omega
