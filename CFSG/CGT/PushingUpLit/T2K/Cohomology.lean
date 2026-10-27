module

public import CFSG.CGT.PushingUpLit.T2K.FourTwo
public import CFSG.Quasithin.Background.JonesParshallSL2

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin.JonesParshall
open scoped commutatorElement

variable {G : Type} [Group G] {L M : Subgroup G} {n : ℕ}

@[expose] def delta (u l : G) : G := u⁻¹ * l * u * l⁻¹

theorem delta_mul (u a b : G) : delta u (a * b) = delta u a * (a * delta u b * a⁻¹) := by
  simp only [delta]
  group

theorem delta_mul_left (u u' l : G) :
    delta (u * u') l = u'⁻¹ * delta u l * u' * delta u' l := by
  simp only [delta]
  group

namespace NatData

variable (D : NatData L n)

open Classical in
noncomputable def ψe (v : G) : Fin 2 → GaloisField 2 n :=
  if hv : v ∈ blockU L then Multiplicative.toAdd (D.ψ ⟨v, hv⟩) else 0

theorem ψe_of_mem {v : G} (hv : v ∈ blockU L) :
    D.ψe v = Multiplicative.toAdd (D.ψ ⟨v, hv⟩) := by simp [ψe, hv]

theorem ψe_mul {a b : G} (ha : a ∈ blockU L) (hb : b ∈ blockU L) :
    D.ψe (a * b) = D.ψe a + D.ψe b := by
  rw [D.ψe_of_mem (mul_mem ha hb), D.ψe_of_mem ha, D.ψe_of_mem hb]
  have : (⟨a * b, mul_mem ha hb⟩ : ↥(blockU L)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem ψe_one : D.ψe 1 = 0 := by
  rw [D.ψe_of_mem (one_mem _)]
  have : (⟨1, one_mem _⟩ : ↥(blockU L)) = 1 := rfl
  rw [this, map_one, toAdd_one]

theorem ψe_inv {a : G} (ha : a ∈ blockU L) : D.ψe a⁻¹ = - D.ψe a := by
  rw [D.ψe_of_mem (inv_mem ha), D.ψe_of_mem ha]
  have : (⟨a⁻¹, inv_mem ha⟩ : ↥(blockU L)) = (⟨a, ha⟩ : ↥(blockU L))⁻¹ := rfl
  rw [this, map_inv, toAdd_inv]

theorem ψe_eq_zero_iff {v : G} (hv : v ∈ blockU L) : D.ψe v = 0 ↔ v ∈ blockZ L := by
  rw [D.ψe_of_mem hv, ← D.ψ_ker ⟨v, hv⟩]
  constructor
  · intro h
    exact Multiplicative.toAdd.injective (by rw [h, toAdd_one])
  · intro h
    rw [h, toAdd_one]

theorem ψe_conj {l : G} (hl : l ∈ L) {v : G} (hv : v ∈ blockU L) :
    D.ψe (l * v * l⁻¹) = ((D.φ ⟨l, hl⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (D.ψe v) := by
  rw [D.ψe_of_mem (conj_mem_blockU (Subgroup.le_normalizer hl) hv), D.ψe_of_mem hv]
  have := D.ψ_conj ⟨l, hl⟩ ⟨v, hv⟩ (conj_mem_blockU (Subgroup.le_normalizer hl) hv)
  rw [this, toAdd_ofAdd]

theorem exists_ψe (w : Fin 2 → GaloisField 2 n) : ∃ v ∈ blockU L, D.ψe v = w := by
  obtain ⟨v, hv⟩ := D.ψ_surj (Multiplicative.ofAdd w)
  refine ⟨v, v.2, ?_⟩
  rw [D.ψe_of_mem v.2, hv, toAdd_ofAdd]

noncomputable def sec : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) → ↥L :=
  Function.surjInv D.φ_surj

theorem φ_sec (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) : D.φ (D.sec g) = g :=
  Function.surjInv_eq D.φ_surj g

noncomputable def κ (u : G) (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    Fin 2 → GaloisField 2 n :=
  D.ψe (delta u (D.sec g : G))

end NatData

namespace NatBlock

variable [Finite G]

theorem delta_mem (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G)) {u l : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) (hl : l ∈ L) :
    delta u l ∈ blockU L := by
  have := h.comm_centralizer_mem_blockU hMN (u := u⁻¹) ⟨M.inv_mem hu.1, Subgroup.inv_mem _ hu.2⟩
    l hl
  simpa [delta, commutatorElement_def, mul_assoc] using this

theorem delta_oTwoIn_mem (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {u o : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) (ho : o ∈ oTwoIn L) :
    delta u o ∈ blockZ L := by
  refine Subgroup.mem_inf.2 ⟨h.delta_mem hMN hu (oTwoIn_le L ho), ?_⟩
  have hoU : o ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) :=
    ⟨hLM (oTwoIn_le L ho), Subgroup.mem_centralizer_iff.2 fun v hv =>
      blockU_comm_of_short h.short v hv o ho⟩
  have := h.comm_mem_centralizer hMN (u := u⁻¹) (u' := o) ⟨M.inv_mem hu.1, Subgroup.inv_mem _ hu.2⟩
    hoU
  simpa [delta, commutatorElement_def, mul_assoc] using this

theorem κ_mul (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G)) {u : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (g g' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    h.natData.κ u (g * g') = h.natData.κ u g +
      ((g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (h.natData.κ u g') := by
  set D := h.natData with hD
  set l : ↥L := D.sec g
  set l' : ↥L := D.sec g'
  set o : ↥L := D.sec (g * g') * (l * l')⁻¹ with ho
  have hoφ : D.φ o = 1 := by
    rw [ho, map_mul, map_inv, map_mul, D.φ_sec, D.φ_sec, D.φ_sec, mul_inv_cancel]
  have hoO : (o : G) ∈ oTwoIn L := (D.φ_ker o).1 hoφ
  have e1 : (D.sec (g * g') : G) = o * ((l : G) * l') := by
    simp only [ho, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hV1 : delta u (l : G) ∈ blockU L := h.delta_mem hMN hu l.2
  have hV2 : delta u (l' : G) ∈ blockU L := h.delta_mem hMN hu l'.2
  have hV3 : delta u ((l : G) * l') ∈ blockU L :=
    h.delta_mem hMN hu (mul_mem l.2 l'.2)
  have hZo : delta u (o : G) ∈ blockZ L := h.delta_oTwoIn_mem hLM hMN hu hoO
  have hconj : (o : G) * delta u ((l : G) * l') * (o : G)⁻¹ = delta u ((l : G) * l') := by
    have := blockU_comm_of_short h.short _ hV3 _ hoO
    rw [← this, mul_inv_cancel_right]
  have hmem : (l : G) * delta u (l' : G) * (l : G)⁻¹ ∈ blockU L :=
    conj_mem_blockU (Subgroup.le_normalizer l.2) hV2
  show D.ψe (delta u (D.sec (g * g') : G)) = D.ψe (delta u (D.sec g : G)) +
      ((g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (D.ψe (delta u (D.sec g' : G)))
  rw [e1, delta_mul, hconj, D.ψe_mul (blockZ_le_blockU L hZo) hV3,
    (D.ψe_eq_zero_iff (blockZ_le_blockU L hZo)).2 hZo, zero_add, delta_mul,
    D.ψe_mul hV1 hmem, D.ψe_conj l.2 hV2]
  have : D.φ ⟨(l : G), l.2⟩ = g := D.φ_sec g
  rw [this]

theorem κ_mem_Z1A (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    h.natData.κ u ∈ Z1A (mu2 (F := GaloisField 2 n)) := fun g g' => by
  rw [h.κ_mul hLM hMN hu g g', mu2_apply]

theorem κ_mul_left (h : NatBlock L n) (hMN : M ≤ Subgroup.normalizer (L : Set G)) {u u' : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (hu' : u' ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    h.natData.κ (u * u') g = h.natData.κ u g + h.natData.κ u' g := by
  set D := h.natData with hD
  have hl : (D.sec g : G) ∈ L := (D.sec g).2
  have hV1 : delta u (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu hl
  have hV2 : delta u' (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu' hl
  have hc : u'⁻¹ * delta u (D.sec g : G) * u' = delta u (D.sec g : G) := by
    have := Subgroup.mem_centralizer_iff.1 hu'.2 _ hV1
    rw [mul_assoc, this, inv_mul_cancel_left]
  show D.ψe (delta (u * u') (D.sec g : G)) = D.ψe (delta u (D.sec g : G)) +
    D.ψe (delta u' (D.sec g : G))
  rw [delta_mul_left, hc, D.ψe_mul hV1 hV2]

theorem κ_apply (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) {l : G} (hl : l ∈ L) :
    h.natData.κ u (h.natData.φ ⟨l, hl⟩) = h.natData.ψe (delta u l) := by
  set D := h.natData with hD
  set g := D.φ ⟨l, hl⟩ with hg
  set o : ↥L := ⟨l, hl⟩ * (D.sec g)⁻¹ with ho
  have hoφ : D.φ o = 1 := by
    rw [ho, map_mul, map_inv, D.φ_sec, hg, mul_inv_cancel]
  have hoO : (o : G) ∈ oTwoIn L := (D.φ_ker o).1 hoφ
  have e1 : l = o * (D.sec g : G) := by
    simp only [ho, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hV1 : delta u (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu (D.sec g).2
  have hZo : delta u (o : G) ∈ blockZ L := h.delta_oTwoIn_mem hLM hMN hu hoO
  have hconj : (o : G) * delta u (D.sec g : G) * (o : G)⁻¹ = delta u (D.sec g : G) := by
    have := blockU_comm_of_short h.short _ hV1 _ hoO
    rw [← this, mul_inv_cancel_right]
  show D.ψe (delta u (D.sec g : G)) = D.ψe (delta u l)
  rw [e1, delta_mul, hconj, D.ψe_mul (blockZ_le_blockU L hZo) hV1,
    (D.ψe_eq_zero_iff (blockZ_le_blockU L hZo)).2 hZo, zero_add]

theorem κ_eq_zero_iff (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    h.natData.κ u = 0 ↔ u ∈ Subgroup.centralizer (L : Set G) := by
  set D := h.natData with hD
  constructor
  · intro h0
    have hZ : ∀ l ∈ L, delta u l ∈ blockZ L := by
      intro l hl
      set g := D.φ ⟨l, hl⟩ with hg
      set o : ↥L := ⟨l, hl⟩ * (D.sec g)⁻¹ with ho
      have hoφ : D.φ o = 1 := by
        rw [ho, map_mul, map_inv, D.φ_sec, hg, mul_inv_cancel]
      have hoO : (o : G) ∈ oTwoIn L := (D.φ_ker o).1 hoφ
      have e1 : l = o * (D.sec g : G) := by
        simp only [ho, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hV1 : delta u (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu (D.sec g).2
      have hZo : delta u (o : G) ∈ blockZ L := h.delta_oTwoIn_mem hLM hMN hu hoO
      have hconj : (o : G) * delta u (D.sec g : G) * (o : G)⁻¹ = delta u (D.sec g : G) := by
        have := blockU_comm_of_short h.short _ hV1 _ hoO
        rw [← this, mul_inv_cancel_right]
      have hZ1 : delta u (D.sec g : G) ∈ blockZ L :=
        (D.ψe_eq_zero_iff hV1).1 (congrFun h0 g)
      rw [e1, delta_mul, hconj]
      exact (blockZ L).mul_mem hZo hZ1
    have hx : u⁻¹ ∈ Subgroup.normalizer (L : Set G) := hMN (M.inv_mem hu.1)
    have key := comm_eq_one_of_perfect h.perfect hx
      (fun l hl => blockZ_le_centralizer L (by
        have := hZ l hl
        simpa [delta, commutatorElement_def, mul_assoc] using this))
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    have h1 := key l hl
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    have h2 : u⁻¹ * l = l * u⁻¹ := h1
    calc l * u = u * (u⁻¹ * l) * u⁻¹⁻¹ := by group
      _ = u * (l * u⁻¹) * u⁻¹⁻¹ := by rw [h2]
      _ = u * l := by group
  · intro hc
    funext g
    show D.ψe (delta u (D.sec g : G)) = 0
    have : delta u (D.sec g : G) = 1 := by
      have hh := Subgroup.mem_centralizer_iff.1 hc _ (D.sec g).2
      calc delta u (D.sec g : G) = u⁻¹ * ((D.sec g : G) * u) * (D.sec g : G)⁻¹ := by
            simp only [delta]; group
        _ = u⁻¹ * (u * (D.sec g : G)) * (D.sec g : G)⁻¹ := by rw [hh]
        _ = 1 := by group
    rw [this, D.ψe_one]

theorem κ_blockU (h : NatBlock L n) {v : G} (hv : v ∈ blockU L)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    h.natData.κ v g = coboundaryA (mu2 (F := GaloisField 2 n)) (h.natData.ψe v) g := by
  set D := h.natData with hD
  have hl : (D.sec g : G) ∈ L := (D.sec g).2
  have hw : (D.sec g : G) * v * (D.sec g : G)⁻¹ ∈ blockU L :=
    conj_mem_blockU (Subgroup.le_normalizer hl) hv
  show D.ψe (delta v (D.sec g : G)) = _
  have e : delta v (D.sec g : G) = v⁻¹ * ((D.sec g : G) * v * (D.sec g : G)⁻¹) := by
    simp only [delta]
    group
  rw [e, D.ψe_mul (inv_mem hv) hw, D.ψe_inv hv, D.ψe_conj hl hv, coboundaryA_apply, mu2_apply]
  have : D.φ ⟨(D.sec g : G), hl⟩ = g := D.φ_sec g
  rw [this]
  abel

theorem relIndex_le (h : NatBlock L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) :
    ((M ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L).relIndex
      (M ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ 2 ^ n := by
  classical
  set D := h.natData with hD
  set U : Subgroup G := M ⊓ Subgroup.centralizer (blockU L : Set G) with hU
  set C : Subgroup G := M ⊓ Subgroup.centralizer (L : Set G) with hC
  have hVU : blockU L ≤ U := fun v hv =>
    ⟨hLM (blockU_le L hv), Subgroup.mem_centralizer_iff.2 fun w hw => h.blockU_comm w hw v hv⟩
  have hCU : C ≤ U := fun c hc => ⟨hc.1, Subgroup.mem_centralizer_iff.2 fun w hw =>
    Subgroup.mem_centralizer_iff.1 hc.2 w (blockU_le L hw)⟩
  let f : ↥U →* Multiplicative ↥(Z1A (mu2 (F := GaloisField 2 n))) :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd ⟨D.κ u, h.κ_mem_Z1A hLM hMN u.2⟩) fun u u' => by
      rw [← ofAdd_add]
      congr 1
      exact Subtype.ext (funext fun g => h.κ_mul_left hMN u.2 u'.2 g)
  have hker : f.ker = C.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hu
      have h0 : D.κ u = 0 := by
        have := congrArg (fun x : Multiplicative ↥(Z1A (mu2 (F := GaloisField 2 n))) =>
          ((Multiplicative.toAdd x : ↥(Z1A (mu2 (F := GaloisField 2 n)))) :
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) → Fin 2 → GaloisField 2 n)) hu
        simpa [f] using this
      exact ⟨u.2.1, (h.κ_eq_zero_iff hLM hMN u.2).1 h0⟩
    · intro hu
      have h0 : D.κ u = 0 := (h.κ_eq_zero_iff hLM hMN u.2).2 hu.2
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      simpa [f] using h0
  set W : Subgroup ↥U := (blockU L).subgroupOf U with hW
  set Hm : Subgroup (Multiplicative ↥(Z1A (mu2 (F := GaloisField 2 n)))) := W.map f with hHm
  have hcomap : Hm.comap f = (C ⊔ blockU L).subgroupOf U := by
    rw [hHm, Subgroup.comap_map_eq, hker, hW, Subgroup.subgroupOf_sup hCU hVU, sup_comm]
  have h1 : (C ⊔ blockU L).relIndex U = Hm.relIndex f.range := by
    have := Subgroup.relIndex_comap Hm f ⊤
    rw [hcomap, Subgroup.relIndex_top_right, Subgroup.map_top] at this
    exact this
  have hHr : Hm ≤ f.range := Subgroup.map_le_range f W
  have h2 := Subgroup.relIndex_mul_card Hm f.range
  rw [inf_of_le_left hHr] at h2
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by have := h.two_le; omega)
  have hZ := card_Z1A_mu2 (F := GaloisField 2 n) hq (by have := h.two_le; omega)
  have hr : Nat.card f.range ≤ Nat.card ↥(Z1A (mu2 (F := GaloisField 2 n))) := by
    have : Nat.card f.range ≤ Nat.card (Multiplicative ↥(Z1A (mu2 (F := GaloisField 2 n)))) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    exact this.trans (le_of_eq (Nat.card_congr Multiplicative.toAdd))
  have hb : Nat.card ↥(B1A (mu2 (F := GaloisField 2 n))) ≤ Nat.card ↥Hm := by
    let ι : ↥(B1A (mu2 (F := GaloisField 2 n))) → ↥Hm := fun b => ⟨Multiplicative.ofAdd
      ⟨b.1, B1A_le_Z1A _ b.2⟩, by
        obtain ⟨w, hw⟩ := b.2
        obtain ⟨v, hv, hvw⟩ := D.exists_ψe w
        refine ⟨⟨v, hVU hv⟩, ?_, ?_⟩
        · exact hv
        · apply Multiplicative.toAdd.injective
          apply Subtype.ext
          funext g
          show D.κ v g = b.1 g
          rw [h.κ_blockU hv g, hvw, ← hw]⟩
    refine Nat.card_le_card_of_injective ι fun b b' hbb => ?_
    apply Subtype.ext
    have := congrArg (fun x : ↥Hm =>
      ((Multiplicative.toAdd (x : Multiplicative ↥(Z1A (mu2 (F := GaloisField 2 n)))) :
        ↥(Z1A (mu2 (F := GaloisField 2 n)))) :
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) → Fin 2 → GaloisField 2 n)) hbb
    simpa [ι] using this
  have hcpos : 0 < Nat.card ↥Hm := Nat.card_pos
  rw [h1]
  have h3 : Hm.relIndex f.range * Nat.card ↥Hm ≤ 2 ^ n * Nat.card ↥Hm := by
    calc Hm.relIndex f.range * Nat.card ↥Hm = Nat.card f.range := h2
      _ ≤ Nat.card ↥(Z1A (mu2 (F := GaloisField 2 n))) := hr
      _ = Fintype.card (GaloisField 2 n) * Nat.card ↥(B1A (mu2 (F := GaloisField 2 n))) := hZ
      _ ≤ 2 ^ n * Nat.card ↥Hm := by rw [hq]; exact Nat.mul_le_mul_left _ hb
  exact Nat.le_of_mul_le_mul_right h3 hcpos

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
