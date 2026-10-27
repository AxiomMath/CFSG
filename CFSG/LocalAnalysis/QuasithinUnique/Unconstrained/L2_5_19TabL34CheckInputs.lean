module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L34
open CFSG.PSL3Four CFSG.PSL3Four.Native

set_option compiler.extract_closed false

@[expose] def cent2Scan : Bool :=
  let ES := enumBFS 42 gensS 20160
  let ER := enumBFS 42 gTabs 241920
  let C := centTabs 42 ES.tabs r₂T
  allBelow ER.tabs.size fun k =>
    !(allBelow C.size fun i => comp 42 ER.tabs[k]! C[i]! == comp 42 C[i]! ER.tabs[k]!) ||
      ER.tabs[k]! == idTab 42 || ER.tabs[k]! == r₂T

@[expose] def twistScan : Bool :=
  let ES := enumBFS 42 gensS 20160
  let C := centTabs 42 ES.tabs r₂T
  allBelow C.size fun j =>
    C[j]! == idTab 42 || !(comp 42 C[j]! C[j]! == idTab 42) ||
      anyBelow ES.tabs.size fun k =>
        (invTab 42 ES.tabs[k]!).size == 42 &&
        comp 42 (invTab 42 ES.tabs[k]!) ES.tabs[k]! == idTab 42 &&
        comp 42 (comp 42 (invTab 42 ES.tabs[k]!) r₂T) ES.tabs[k]! == comp 42 r₂T C[j]!

end CFSG.QuasithinUnique.Id2519.Tab.L34
