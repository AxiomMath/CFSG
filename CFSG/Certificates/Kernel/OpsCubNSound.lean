module

public import Certificates.Data.Kernel.OpsCubN
public import CFSG.Certificates.Kernel.OpsMcertNSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.OpsCubN

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.OpsMN CFSG.KC.OpsHom CFSG.KC.Loop

section Twin

variable (O : Ops Nat Nat)

theorem pwN_eq (X e : Nat) : pwN O X e = O.pow X e := powN_eq O _ _ _ (Nat.lt_succ_self e)

theorem appN_eq (X : Nat) : ∀ (n v : Nat), appN O X n v = O.app X n v
  | 0, _ => rfl
  | n + 1, v => by
    change strictN (O.vmul v X) (appN O X n) = O.app X n (O.vmul v X)
    rw [strictN_eq, appN_eq X n]

theorem appBaseN_eq (b : Nat) : ∀ (xs : List Nat) (n v : Nat),
    appBaseN O b xs n v = O.appBase b xs n v
  | [], _, _ => rfl
  | X :: xs, n, v => by
    change appBaseN O b xs (n / b) (appN O X (n % b) v) = O.appBase b xs (n / b) (O.app X (n % b) v)
    rw [appN_eq, appBaseN_eq b xs]

theorem pairN_cons (v : Nat) (vs : List Nat) :
    pairN O (v :: vs) = (vs.all (fun w => O.vne v w) && pairN O vs) := rfl

theorem pairN_spec (g : Nat → Nat) : ∀ N, pairN O ((List.range N).map g).reverse = true →
    ∀ i < N, ∀ j < i, O.vne (g i) (g j) = true
  | 0, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | N + 1, h, i, hi, j, hj => by
    rw [List.range_succ, List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_singleton, List.singleton_append, pairN_cons, Bool.and_eq_true,
      List.all_eq_true] at h
    by_cases hiN : i = N
    · subst hiN
      exact h.1 (g j) (List.mem_reverse.2 (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
    · exact pairN_spec g N h.2 i (by omega) j hj

end Twin

section Hom

variable {M V₀ : Type} [Inhabited M] [Inhabited V₀] {O₀ : Ops M V₀} {O : Ops Nat Nat}
  (H : Hom O₀ O)

omit [Inhabited M] in
theorem normalFormOK_of_N (b : Nat) {xs : List Nat} (hxs : ∀ x ∈ xs, H.P x) (t : Nat)
    (h : nfN O b xs t = true) : O₀.normalFormOK b (xs.map H.U) t = true := by
  unfold nfN at h
  rw [forceL_eq] at h
  have hd := pairN_spec O (fun n => appBaseN O b xs n (O.unit t)) _ h
  obtain ⟨eu, qu⟩ := H.unit t
  unfold Ops.normalFormOK Ops.distinctOK
  rw [List.length_map]
  simp only [List.all_eq_true, List.mem_range, Array.size_ofFn]
  intro i hi j hj
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ j (by simp; omega),
    Array.getElem_ofFn, Array.getElem_ofFn, eu]
  obtain ⟨ei, qi⟩ := H.appBase_U b xs hxs i qu
  obtain ⟨ej, qj⟩ := H.appBase_U b xs hxs j qu
  rw [ei, ej, H.vne qi qj, ← appBaseN_eq, ← appBaseN_eq]
  exact hd i hi j hj

theorem cubicCheck_of_N {A B : Nat} {D : CubData} (eA : O₀.decode D.seedA = H.U A)
    (eB : O₀.decode D.seedB = H.U B) (hA : H.P A) (hB : H.P B)
    (h : cubicN O A B D = true) : O₀.cubicCheck D = true := by
  unfold cubicN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, hp⟩, hx⟩, hy⟩, hh⟩, hr⟩, ho⟩, hrun⟩ := h
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N H eA eB hA hB hp hrun
  obtain ⟨eX, pX⟩ := hR.2 D.rx (by rw [hlen]; exact hx)
  obtain ⟨eY, pY⟩ := hR.2 D.ry (by rw [hlen]; exact hy)
  obtain ⟨eH, pH⟩ := hR.2 D.rh (by rw [hlen]; exact hh)
  unfold cubN at hk
  rw [forceB_eq] at hk
  generalize getN Rl D.rx = X at eX pX hk
  generalize getN Rl D.ry = Y at eY pY hk
  generalize getN Rl D.rh = Hm at eH pH hk
  unfold cubZ at hk
  simp only [pwN_eq, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hXr, hYr⟩, hHo⟩, hmv⟩, hZX⟩, hZY⟩, hcX⟩, hcY⟩, hcZ⟩, hnf⟩ := hk
  obtain ⟨m1, q1⟩ := H.mul pX pY
  obtain ⟨m2, q2⟩ := H.pow_U (D.r - 1) pX
  obtain ⟨m3, q3⟩ := H.mul q1 q2
  obtain ⟨m4, q4⟩ := H.pow_U (D.r - 1) pY
  obtain ⟨m5, pZ⟩ := H.mul q3 q4
  generalize O.mul (O.mul (O.mul X Y) (O.pow X (D.r - 1)))
    (O.pow Y (D.r - 1)) = Z at m5 pZ hZX hZY hcX hcY hcZ hnf hmv
  have eZ : O₀.commM D.r (H.U X) (H.U Y) = H.U Z := by
    unfold Ops.commM
    rw [m1, m2, m3, m4, m5]
  obtain ⟨xr, pxr⟩ := H.pow_U D.r pX
  obtain ⟨yr, pyr⟩ := H.pow_U D.r pY
  obtain ⟨ho', pho⟩ := H.pow_U D.oh pH
  obtain ⟨xa, pxa⟩ := H.pow_U D.a pX
  obtain ⟨yb, pyb⟩ := H.pow_U D.b pY
  obtain ⟨zk, pzk⟩ := H.pow_U D.k pZ
  obtain ⟨xc, pxc⟩ := H.pow_U D.c pX
  obtain ⟨yd, pyd⟩ := H.pow_U D.d pY
  obtain ⟨zl, pzl⟩ := H.pow_U D.l pZ
  obtain ⟨zμ, pzμ⟩ := H.pow_U D.μ pZ
  obtain ⟨a1, pa1⟩ := H.mul pxa pyb
  obtain ⟨a2, pa2⟩ := H.mul pa1 pzk
  obtain ⟨c1, pc1⟩ := H.mul pxc pyd
  obtain ⟨c2, pc2⟩ := H.mul pc1 pzl
  obtain ⟨hx1, phx1⟩ := H.mul pH pX
  obtain ⟨hx2, phx2⟩ := H.mul pa2 pH
  obtain ⟨hy1, phy1⟩ := H.mul pH pY
  obtain ⟨hy2, phy2⟩ := H.mul pc2 pH
  obtain ⟨hz1, phz1⟩ := H.mul pH pZ
  obtain ⟨hz2, phz2⟩ := H.mul pzμ pH
  obtain ⟨zx, pzx⟩ := H.mul pZ pX
  obtain ⟨xz, pxz⟩ := H.mul pX pZ
  obtain ⟨zy, pzy⟩ := H.mul pZ pY
  obtain ⟨yz, pyz⟩ := H.mul pY pZ
  obtain ⟨eu, qu⟩ := H.unit D.t
  obtain ⟨ev, qv⟩ := H.vmul qu pZ
  have hnf' := normalFormOK_of_N H D.r (xs := [X, Y, Z])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl | rfl) <;>
      assumption) D.t hnf
  unfold Ops.cubicCheck Ops.conjOK
  simp only [eX, eY, eH, eZ, Bool.and_eq_true, decide_eq_true_eq]
  rw [xr, yr, ho', xa, yb, zk, xc, yd, zl, zμ, a1, a2, c1, c2, hx1, hx2, hy1, hy2, hz1, hz2, zx, xz,
    zy, yz, eu, ev, H.one.1, H.eq pxr H.one.2, H.eq pyr H.one.2, H.eq pho H.one.2, H.vne qv qu,
    H.eq pzx pxz, H.eq pzy pyz, H.eq phx1 phx2, H.eq phy1 phy2, H.eq phz1 phz2]
  simp only [List.map_cons, List.map_nil] at hnf'
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hp⟩, hx⟩, hy⟩, hh⟩, hr⟩, ho⟩, hXr⟩, hYr⟩, hHo⟩, hmv⟩, hZX⟩, hZY⟩,
    hcX⟩, hcY⟩, hcZ⟩, hnf'⟩

end Hom

end CFSG.KC.OpsCubN

end
