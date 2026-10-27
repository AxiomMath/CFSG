module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Sub
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open

theorem mem_lstT {p : Pc} : p ∈ lstT ↔ ∃ i < 9, ∃ j < 9, ∃ k < 3, p = nf i j k := by
  simp [lstT, List.mem_flatMap, eq_comm]

theorem mem_lstA {p : Pc} : p ∈ lstA ↔ ∃ a < 3, ∃ b < 3, ∃ c < 3, p = nf (3 * a) (3 * b) c := by
  simp [lstA, List.mem_flatMap, eq_comm]

theorem mem_lstE {p : Pc} : p ∈ lstE ↔ ∃ a < 3, ∃ b < 3, p = nf (3 * a) (3 * b) 0 := by
  simp [lstE, List.mem_flatMap, eq_comm]

theorem length_lstT : lstT.length = 243 := by simp [lstT]

theorem length_lstA : lstA.length = 27 := by simp [lstA]

theorem length_lstE : lstE.length = 9 := by simp [lstE]

theorem eq_of_code {p q : Pc} {x y : Hh} (hx : RepP p x) (hy : RepP q y) (h : p = q) : x = y :=
  hx.eq (h ▸ hy)

structure NF : Prop where
  nodupT : lstT.Nodup
  nodupE : lstE.Nodup
  nodupA : lstA.Nodup
  oneT : oneP ∈ lstT
  oneA : oneP ∈ lstA
  mulT : ∀ p ∈ lstT, ∀ q ∈ lstT, mulP p q ∈ lstT
  powT : ∀ p ∈ lstT, powP p 9 = oneP ∧ powP p 8 ∈ lstT
  mulA : ∀ p ∈ lstA, ∀ q ∈ lstA, mulP p q ∈ lstA
  subA : ∀ p ∈ lstA, p ∈ lstT ∧ powP p 2 ∈ lstA
  subE : ∀ p ∈ lstE, p ∈ lstA

theorem nf_of_check (h : normalFormOK = true) : NF := by
  simp [normalFormOK, and_assoc] at h
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

structure Ord3 : Prop where
  pow3 : ∀ p ∈ lstA, powP p 3 = oneP
  commA : ∀ p ∈ lstA, ∀ q ∈ lstA, mulP p q = mulP q p
  order3 : ∀ p ∈ lstT, p.j = 0 → powP p 3 = oneP → p ∈ lstE

theorem ord3_of_check (h : ordThreeOK = true) : Ord3 := by
  simp [ordThreeOK] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  refine ⟨a, b, fun p hp hj h3 => ?_⟩
  rcases c p hp with (h | h) | h
  · exact absurd hj h
  · exact absurd h3 h
  · exact h

structure Centre : Prop where
  central : ∀ p ∈ lstE, ∀ q ∈ lstT, mulP p q = mulP q p
  inE : ∀ p ∈ lstT, mulP p t1c = mulP t1c p → mulP p t2c = mulP t2c p →
    mulP p fc = mulP fc p → p ∈ lstE

theorem centre_of_check (h : centreOK = true) : Centre := by
  simp [centreOK] at h
  obtain ⟨a, b⟩ := h
  refine ⟨a, fun p hp h1 h2 h3 => ?_⟩
  rcases b p hp with (h | h | h) | h
  · exact absurd h1 h
  · exact absurd h2 h
  · exact absurd h3 h
  · exact h

structure NormC (b bi : Pc) : Prop where
  inv : mulP b bi = oneP
  normT : ∀ p ∈ lstT, mulP (mulP b p) bi ∈ lstT
  normE : ∀ p ∈ lstE, mulP (mulP b p) bi ∈ lstE

structure NormAll : Prop where
  t1 : NormC t1c (powP t1c 8)
  t2 : NormC t2c (powP t2c 8)
  w : NormC wc wc
  s : NormC sc sc
  f : NormC fc (powP fc 2)

theorem norm_of_check (h : normalOK = true) : NormAll := by
  simp [normalOK, and_assoc] at h
  obtain ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, e1, e2, e3⟩ := h
  exact ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩, ⟨e1, e2, e3⟩⟩

theorem orbit_of_check (h : orbitOK = true) :
    ∀ p ∈ lstA, p ∈ lstE ∨ ∀ k < 4, ∀ l < 4, k = l ∨
      (cj k p ≠ oneP ∧ cj k p ≠ cj l p) ∧ cj k p ≠ mulP (cj l p) (cj l p) := by
  simpa [orbitOK] using h

theorem hom_of_check (h : homOK = true) :
    ∀ a < 9, ∀ b < 9, powP t1c a ≠ powP t2c b ∨ a = 0 := by
  simpa [homOK] using h

structure Rels : Prop where
  t1_9 : gt1 ^ 9 = 1
  t2_9 : gt2 ^ 9 = 1
  f_3 : gf ^ 3 = 1
  t1_3 : gt1 ^ 3 ≠ 1
  t12 : gt1 * gt2 = gt2 * gt1
  ft1 : gf * gt1 = gt1 ^ 7 * gf
  ft2 : gf * gt2 = gt2 ^ 7 * gf
  ww : gw * gw = 1
  ss : gs * gs = 1
  wt1 : gw * gt1 * gw = gt1 ^ 8
  wt2 : gw * gt2 = gt2 * gw
  wf : gw * gf = gf * gw
  st1 : gs * gt1 * gs = gt2
  st2 : gs * gt2 * gs = gt1
  sf : gs * gf = gf * gs

theorem rels_of_check (hg : gensValid = true) (hr : relOK = true) : Rels := by
  have r1 := repP_gt1 hg
  have r2 := repP_gt2 hg
  have rw := repP_gw hg
  have rs := repP_gs hg
  have rf := repP_gf
  simp [relOK, and_assoc] at hr
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := hr
  refine ⟨eq_of_code (r1.pow 9) RepP.one e1, eq_of_code (r2.pow 9) RepP.one e2,
    eq_of_code (rf.pow 3) RepP.one e3, fun hh => e4 ?_, eq_of_code (r1.mul r2) (r2.mul r1) e5,
    eq_of_code (rf.mul r1) ((r1.pow 7).mul rf) e6, eq_of_code (rf.mul r2) ((r2.pow 7).mul rf) e7,
    eq_of_code (rw.mul rw) RepP.one e8, eq_of_code (rs.mul rs) RepP.one e9,
    eq_of_code ((rw.mul r1).mul rw) (r1.pow 8) e10, eq_of_code (rw.mul r2) (r2.mul rw) e11,
    eq_of_code (rw.mul rf) (rf.mul rw) e12, eq_of_code ((rs.mul r1).mul rs) r2 e13,
    eq_of_code ((rs.mul r2).mul rs) r1 e14, eq_of_code (rs.mul rf) (rf.mul rs) e15⟩
  have := (r1.pow 3)
  rw [hh] at this
  exact this.code_eq RepP.one

@[expose] noncomputable def nfElt (i j k : ℕ) : Hh := gt1 ^ i * gt2 ^ j * gf ^ k

theorem repP_nfElt (hg : gensValid = true) (i j k : ℕ) : RepP (nf i j k) (nfElt i j k) :=
  (((repP_gt1 hg).pow i).mul ((repP_gt2 hg).pow j)).mul (repP_gf.pow k)

theorem card_of_codes {H : Subgroup Hh} {L : List Pc} (hH : ∀ x, x ∈ H ↔ ∃ p ∈ L, RepP p x)
    (hnd : L.Nodup) (hex : ∀ p ∈ L, ∃ x : Hh, RepP p x) : Nat.card H = L.length := by
  classical
  let code : H → Pc := fun x => Classical.choose ((hH x.1).1 x.2)
  have hcode : ∀ x : H, code x ∈ L ∧ RepP (code x) x.1 :=
    fun x => Classical.choose_spec ((hH x.1).1 x.2)
  have hinj : Function.Injective code := by
    intro x y h
    apply Subtype.ext
    exact (hcode x).2.eq (h ▸ (hcode y).2)
  have hrange : Set.range code = {p | p ∈ L} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact (hcode x).1
    · intro hp
      obtain ⟨x, hx⟩ := hex p hp
      refine ⟨⟨x, (hH x).2 ⟨p, hp, hx⟩⟩, ?_⟩
      exact (hcode ⟨x, (hH x).2 ⟨p, hp, hx⟩⟩).2.code_eq hx
  rw [← Nat.card_range_of_injective hinj, hrange, Nat.card_coe_set_eq]
  have : {p | p ∈ L} = ((L.toFinset : Finset Pc) : Set Pc) := by ext; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

section Groups

variable (hg : gensValid = true) (hnf : NF) (ho : Ord3) (hc : Centre)

@[expose] noncomputable def Th : Subgroup Hh :=
  codeSubgroup lstT hnf.oneT hnf.mulT (fun p hp => ⟨8, (hnf.powT p hp).1, (hnf.powT p hp).2⟩)

@[expose] noncomputable def Ah : Subgroup Hh :=
  codeSubgroup lstA hnf.oneA hnf.mulA
    (fun p hp => ⟨2, ho.pow3 p hp, (hnf.subA p hp).2⟩)

@[expose] noncomputable def Eh : Subgroup Hh := centerOf (Th hnf)

@[expose] noncomputable def Th0 : Subgroup Hh :=
  Th hnf ⊓ (SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3))
    (φ := phi)).ker

include hg in
theorem mem_Th {x : Hh} : x ∈ Th hnf ↔ ∃ i < 9, ∃ j < 9, ∃ k < 3, x = nfElt i j k := by
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_lstT.1 hp
    exact ⟨i, hi, j, hj, k, hk, hx.eq (repP_nfElt hg i j k)⟩
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩
    exact ⟨nf i j k, mem_lstT.2 ⟨i, hi, j, hj, k, hk, rfl⟩, repP_nfElt hg i j k⟩

include hg in
theorem mem_Ah {x : Hh} : x ∈ Ah hnf ho ↔
    ∃ a < 3, ∃ b < 3, ∃ c < 3, x = nfElt (3 * a) (3 * b) c := by
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_lstA.1 hp
    exact ⟨a, ha, b, hb, c, hc, hx.eq (repP_nfElt hg _ _ _)⟩
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    exact ⟨nf (3 * a) (3 * b) c, mem_lstA.2 ⟨a, ha, b, hb, c, hc, rfl⟩, repP_nfElt hg _ _ _⟩

include hg in
theorem gt1_mem : gt1 ∈ Th hnf := by
  rw [mem_Th hg hnf]
  exact ⟨1, by norm_num, 0, by norm_num, 0, by norm_num, by simp [nfElt]⟩

include hg in
theorem gt2_mem : gt2 ∈ Th hnf := by
  rw [mem_Th hg hnf]
  exact ⟨0, by norm_num, 1, by norm_num, 0, by norm_num, by simp [nfElt]⟩

include hg in
theorem gf_mem : gf ∈ Th hnf := by
  rw [mem_Th hg hnf]
  exact ⟨0, by norm_num, 0, by norm_num, 1, by norm_num, by simp [nfElt]⟩

include hg hc in
theorem mem_Eh_code {x : Hh} : x ∈ Eh hnf ↔ ∃ p ∈ lstE, RepP p x := by
  constructor
  · rintro ⟨hxT, hxC⟩
    obtain ⟨p, hp, hx⟩ := hxT
    have hcomm : ∀ {q : Pc} {y : Hh}, RepP q y → y ∈ Th hnf → mulP q p = mulP p q := by
      intro q y hy hyT
      have := Subgroup.mem_centralizer_iff.1 hxC y hyT
      exact (hy.mul hx).code_eq (by rw [this]; exact hx.mul hy)
    refine ⟨p, hc.inE p hp ?_ ?_ ?_, hx⟩
    · exact (hcomm (repP_gt1 hg) (gt1_mem hg hnf)).symm
    · exact (hcomm (repP_gt2 hg) (gt2_mem hg hnf)).symm
    · exact (hcomm repP_gf (gf_mem hg hnf)).symm
  · rintro ⟨p, hp, hx⟩
    have hxT : x ∈ Th hnf := ⟨p, (mem_lstT.2 (by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_lstE.1 hp
      exact ⟨3 * a, by omega, 3 * b, by omega, 0, by norm_num, rfl⟩)), hx⟩
    refine ⟨hxT, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨q, hq, hy'⟩ := hy
    exact eq_of_code (hy'.mul hx) (hx.mul hy') (hc.central p hp q hq).symm

include hg hc in
theorem mem_Eh {x : Hh} : x ∈ Eh hnf ↔ ∃ a < 3, ∃ b < 3, x = nfElt (3 * a) (3 * b) 0 := by
  rw [mem_Eh_code hg hnf hc]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_lstE.1 hp
    exact ⟨a, ha, b, hb, hx.eq (repP_nfElt hg _ _ _)⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨nf (3 * a) (3 * b) 0, mem_lstE.2 ⟨a, ha, b, hb, rfl⟩, repP_nfElt hg _ _ _⟩

include hg in
theorem card_Th : Nat.card (Th hnf) = 243 := by
  rw [← length_lstT]
  refine card_of_codes (fun x => Iff.rfl) hnf.nodupT fun p hp => ?_
  obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_lstT.1 hp
  exact ⟨_, repP_nfElt hg i j k⟩

include hg in
theorem card_Ah : Nat.card (Ah hnf ho) = 27 := by
  rw [← length_lstA]
  refine card_of_codes (fun x => Iff.rfl) hnf.nodupA fun p hp => ?_
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_lstA.1 hp
  exact ⟨_, repP_nfElt hg _ _ _⟩

include hg hc in
theorem card_Eh : Nat.card (Eh hnf) = 9 := by
  rw [← length_lstE]
  refine card_of_codes (fun x => mem_Eh_code hg hnf hc) hnf.nodupE fun p hp => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_lstE.1 hp
  exact ⟨_, repP_nfElt hg _ _ _⟩


theorem rightHom_nfElt (i j k : ℕ) :
    SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3)) (φ := phi)
      (nfElt i j k) = Multiplicative.ofAdd ((k : ℕ) : ZMod 3) := by
  have h1 : SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3)) (φ := phi)
      gt1 = 1 := SemidirectProduct.rightHom_inl _
  have h2 : SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3)) (φ := phi)
      gt2 = 1 := SemidirectProduct.rightHom_inl _
  have h3 : SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3)) (φ := phi)
      gf = Multiplicative.ofAdd (1 : ZMod 3) := SemidirectProduct.rightHom_inr _
  simp only [nfElt, map_mul, map_pow, h1, h2, h3, one_pow, one_mul]
  rw [← ofAdd_nsmul]
  simp

theorem nfElt_mem_ker_iff (i j k : ℕ) (hk : k < 3) :
    nfElt i j k ∈ (SemidirectProduct.rightHom (N := Sp8) (G := Multiplicative (ZMod 3))
      (φ := phi)).ker ↔ k = 0 := by
  rw [MonoidHom.mem_ker, rightHom_nfElt]
  constructor
  · intro h
    have : ((k : ℕ) : ZMod 3) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [ZMod.natCast_eq_zero_iff] at this
    omega
  · rintro rfl
    simp

include hg in
theorem mem_Th0 {x : Hh} : x ∈ Th0 hnf ↔ ∃ i < 9, ∃ j < 9, x = nfElt i j 0 := by
  constructor
  · rintro ⟨hxT, hxk⟩
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := (mem_Th hg hnf).1 hxT
    have := (nfElt_mem_ker_iff i j k hk).1 hxk
    subst this
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨(mem_Th hg hnf).2 ⟨i, hi, j, hj, 0, by norm_num, rfl⟩,
      (nfElt_mem_ker_iff i j 0 (by norm_num)).2 rfl⟩

theorem right_eq_one_iff {q : Pc} {x : Hh} (hx : RepP q x) : x.right = 1 ↔ q.j = 0 := by
  rw [hx.exp]
  constructor
  · intro h
    simp [h]
  · intro h
    have : Multiplicative.toAdd x.right = 0 := (ZMod.val_eq_zero _).1 h
    exact Multiplicative.toAdd.injective (by simpa using this)

theorem mem_Th0_iff {x : Hh} : x ∈ Th0 hnf ↔ x ∈ Th hnf ∧ x.right = 1 := by
  rw [Th0, Subgroup.mem_inf, MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right]

include hg in
theorem card_Th0 : Nat.card (Th0 hnf) = 81 := by
  have hnd : (lstT.filter fun p => p.j == 0).Nodup := hnf.nodupT.filter _
  have hlen : (lstT.filter fun p => p.j == 0).length = 81 := by decide +kernel
  rw [← hlen]
  refine card_of_codes (fun x => ?_) hnd fun p hp => ?_
  · rw [mem_Th0_iff]
    constructor
    · rintro ⟨⟨q, hq, hxq⟩, hxk⟩
      exact ⟨q, List.mem_filter.2 ⟨hq, by simpa using (right_eq_one_iff hxq).1 hxk⟩, hxq⟩
    · rintro ⟨q, hq, hxq⟩
      obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
      exact ⟨⟨q, hq1, hxq⟩, (right_eq_one_iff hxq).2 (by simpa using hq2)⟩
  · obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := mem_lstT.1 hp1
    exact ⟨_, repP_nfElt hg i j k⟩

end Groups

end CFSG.AGLEmbedding.KFactProofs.Sp48
